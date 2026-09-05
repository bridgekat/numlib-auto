import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Projection
import Numlib.Approximation.BestApprox

/-!
# The power method and subspace iteration

The power iteration `x_{k+1} = A x_k / ‖A x_k‖`, written in closed form
`Krylov.powerIterate A x₀ k = ‖A^k x₀‖⁻¹ • A^k x₀` as a function of the step index, and its
convergence to the dominant eigendirection
(Saad, *Numerical Methods for Large Eigenvalue Problems*[^saad-eigenvalue], Thm 4.1;
Kress[^kress] §7.2); then its block form, subspace iteration
(Saad, Thm 5.2; Kress Lemma 7.18), which carries a whole subspace along and captures as many
dominant eigenvectors as that subspace has dimensions.

## The convergence theorem

Write the starting vector as `x₀ = u + w` with `A u = λ u` and `w` in the invariant subspace
`W = ⨆_{μ ≠ λ} maxGenEigenspace A μ` spanned by the *other* generalized eigenspaces. If every
eigenvalue `μ ≠ λ` has `‖μ‖ < ‖λ‖`, then

* `Krylov.powerIterate_tendsto`: `λ^{-k} A^k x₀ → u`, and
* `Krylov.exists_norm_inv_pow_smul_pow_apply_sub_le`: the error is `O((r/‖λ‖)^k)` for every `r`
  above the moduli of the other eigenvalues — the classical rate `|λ₂/λ₁|^k`, weakened to a
  strict bound because a subdominant Jordan block contributes a polynomial factor.

Three features of the formulation are deliberate.

*No finite dimension and no algebraically closed field.* Those enter only through
`Krylov.exists_eq_add_mem_maxGenEigenspace`, which splits every `x₀` as `u + w`, and are packaged
in `Krylov.exists_eq_add_tendsto`.

*Semi-simplicity is local to `x₀`.* The cited sources assume the dominant eigenvalue `λ` is
semi-simple, that is, that its generalized eigenspace is its eigenspace. What the proof uses is
only that *the `λ`-component of this particular `x₀`* is an honest eigenvector — the hypothesis
`A u = λ u`. Semi-simplicity delivers that for every `x₀`, and is the hypothesis of
`Krylov.exists_eq_add_tendsto`; a simple eigenvalue is semi-simple by
`Krylov.maxGenEigenspace_eq_eigenspace_of_finrank_eq_one`.

*No Jordan form and no Gelfand formula.* The decay of the subdominant part is
`Krylov.exists_norm_pow_apply_le_of_mem_maxGenEigenspace`: if `(A - μ)^N w = 0` and `‖μ‖ < r`
then `‖A^k w‖ ≤ C r^k`, by induction on `N` from the scalar recursion
`a_{k+1} ≤ ‖μ‖ a_k + C r^k`. The spectrum of a restriction is never computed, `E` need not be
complete and `A` need not be continuous.

## Normalization and phase

`powerIterate` normalizes by a *norm*, so it is unchanged by a positive rescaling of `x₀`
(`Krylov.powerIterate_ofReal_smul`) and satisfies the normalize-at-every-step recurrence exactly,
with no scalar left over to correct for (`Krylov.powerIterate_succ`, and
`Krylov.eq_powerIterate_of_recurrence` for the converse). The convention `(0 : ℝ)⁻¹ = 0` makes it
total: the degenerate case `A^k x₀ = 0` returns `0`, and no statement below has to exclude it.

A norm-normalized iterate cannot converge on the nose, because each step multiplies the
eigendirection by the unimodular scalar `λ/‖λ‖`. Saad's own algorithm sidesteps this by dividing
instead by the entry of largest modulus, which is a *complex* scalar; the notion he introduces for
the general case is that `x_k` **converges essentially** to `x` when `c_k x_k → x` for some
sequence `c_k` of scalars of modulus one. That is what holds here, with the sequence explicit:
`Krylov.tendsto_smul_powerIterate` divides out `(λ/‖λ‖)^k` and
`Krylov.exists_norm_eq_one_tendsto_smul_powerIterate` is the existential form. The phase-free
alternative is `Krylov.tendsto_norm_sub_smul_powerIterate`: the eigenvalue residual
`‖A x_k - λ x_k‖` tends to `0`, so the iterates are approximate eigenvectors for `λ`.

## Inverse iteration

`Krylov.inverseIterate A σ x₀ k` is the power method run on `(A - σ)⁻¹`, the shift-and-invert
iteration of Saad, *Numerical Methods for Large Eigenvalue Problems*[^saad-eigenvalue],
§4.1.2–4.1.3.
Its point is that the map `μ ↦ (μ - σ)⁻¹` makes the eigenvalue of `A` *nearest the shift* the
dominant one, so `Krylov.tendsto_smul_inverseIterate` converges under a hypothesis about distances
to `σ` rather than about moduli, at the rate `(‖λ - σ‖/‖μ₂ - σ‖)^k` — which a shift close to `λ`
makes as fast as one likes.

The inverse is `Ring.inverse`, so `inverseIterate` is total, and `IsUnit (A - σ)` — in finite
dimension, `σ ∉ spectrum 𝕜 A` — is a hypothesis of the theorems rather than of the definition.
The spectral correspondence is proved by hand and needs no spectral mapping theorem: an eigenvector
of `A` for `μ ≠ σ` is an eigenvector of the shifted inverse for `(μ - σ)⁻¹`
(`Krylov.inverse_apply_eq_smul`), a *generalized* eigenvector likewise and with the same index
(`Krylov.maxGenEigenspace_le_maxGenEigenspace_inverse`, from the factorization
`(A - σ)⁻¹ - (μ - σ)⁻¹ = -(μ - σ)⁻¹ (A - σ)⁻¹ (A - μ)` and the commutation of the two factors),
and every eigenvalue of the shifted inverse arises this way
(`Krylov.hasEigenvalue_of_hasEigenvalue_inverse`). Rayleigh quotient iteration, which updates the
shift at every step, is described by the book without a theorem and is not formalized.

## Subspace iteration

`Krylov.subspaceIterate A S₀ k = A^k S₀` is the block form of the same iteration. Bauer's
Treppeniteration reorthonormalizes its block of vectors at every step, which replaces the basis
but not the subspace it spans, so in closed form the `k`-th iterate is again a power of `A`
applied to the starting data — this time to a whole subspace. What converges is the subspace, and
the theorem of Saad, *Numerical Methods for Large Eigenvalue Problems*[^saad-eigenvalue], Thm 5.2
measures its distance to a dominant eigenvector `u`, namely `‖u - P_{S_k} u‖` for `P_{S_k}` the
orthogonal projector onto `S_k`. It is *not* a statement about a gap between subspaces.

* `Krylov.norm_sub_starProjection_subspaceIterate_le` is the analytic core, and it is spectrum-free:
  if `A u = λ u`, if `s ∈ S₀`, and if the orbit of `s - u` obeys `‖A^k (s - u)‖ ≤ C r^k`, then
  `‖u - P_{S_k} u‖ ≤ C (r/‖λ‖)^k`. The single candidate `λ^{-k} A^k s ∈ S_k` proves it, because the
  orthogonal projection is the best approximation from `S_k` and the candidate's error is
  `λ^{-k} A^k (s - u)`.
* `Krylov.exists_norm_sub_starProjection_subspaceIterate_le` is the packaged form, where a
  predicate `p` selects the dominant eigenvalues, `s` comes from the spectral projector below and
  the decay hypothesis from `Krylov.exists_norm_pow_apply_le_of_mem_iSup`. The book's rate
  `(|λ_{m+1}/λ_i| + ε_k)^k` becomes `C (r/‖λ‖)^k` for any `r` above the moduli of the *unselected*
  eigenvalues, which is the same trade as in the power method above: a constant in place of a
  vanishing perturbation of the exponent's base.
* `Krylov.tendsto_starProjection_subspaceIterate` is the convergence it states, under the
  dominance `r < ‖λ‖` that makes the rate a contraction.

The gap of `Numlib.Analysis.InnerProductSpace.Projection.Angle` says more than any of these:
`Submodule.sinAngle_le_gap` turns a bound on `gap M S_k` into the same distance bound for *every*
vector of the dominant invariant subspace `M`, whereas the theorem above gives it only for the
eigenvectors of `M`. That stronger statement is a real theorem of the literature — Kress,
*Numerical Analysis*[^kress], Lemma 7.18, for diagonalizable `A` — and it is not proved here; the
route and what it still needs are recorded in the plan.

## The spectral projector of a set of eigenvalues

The projector `P` onto the invariant subspace of the selected eigenvalues is what turns the
starting subspace `S₀` into the data the bound needs. `Krylov.isCompl_iSup_maxGenEigenspace` splits
`V` as `M ⊕ W`, the supremum of the generalized eigenspaces whose eigenvalue satisfies `p` against
the supremum of the rest, and `Krylov.spectralProjector` is the resulting *oblique* projector,
`Submodule.projection` of that decomposition; `Submodule.starProjection` is the wrong object here,
the splitting being non-orthogonal unless `A` is normal. Its kernel is `W`, so the book's
hypothesis that the vectors `P x_i` are linearly independent is `Disjoint S₀ W`
(`Krylov.injOn_spectralProjector_iff`), and with `finrank S₀ = finrank M` every `u ∈ M` is `P s`
for exactly one `s ∈ S₀` (`Krylov.existsUnique_mem_spectralProjector_eq`).

## References

[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
-/

open Filter Topology

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### The power iteration -/

/-- The power iteration `x_{k+1} = A x_k / ‖A x_k‖` in closed form: the `k`-th iterate is the
normalization of `A^k x₀`.

The scalar is `(‖A^k x₀‖ : 𝕜)⁻¹`, so with the convention `(0 : ℝ)⁻¹ = 0` the definition is total
and returns `0` once `A^k x₀ = 0`; every statement below therefore needs no hypothesis excluding
that case. -/
noncomputable def powerIterate (A : Module.End 𝕜 E) (x₀ : E) (k : ℕ) : E :=
  (‖(A ^ k) x₀‖ : 𝕜)⁻¹ • (A ^ k) x₀

variable (A : Module.End 𝕜 E) (x₀ : E) (k : ℕ)

@[simp]
theorem powerIterate_zero : powerIterate A x₀ 0 = (‖x₀‖ : 𝕜)⁻¹ • x₀ := by
  simp [powerIterate]

/-- The iterate is a scalar multiple of `A^k x₀`, so it spans the same line and lies in the
Krylov subspace `𝒦[A, x₀] (k + 1)`. -/
theorem powerIterate_eq_smul :
    powerIterate A x₀ k = (‖(A ^ k) x₀‖ : 𝕜)⁻¹ • (A ^ k) x₀ := rfl

theorem powerIterate_eq_zero_iff : powerIterate A x₀ k = 0 ↔ (A ^ k) x₀ = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [powerIterate, h]⟩
  by_contra hne
  rw [powerIterate, smul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero] at h
  exact h.elim hne hne

/-- Away from the degenerate case the iterate is a unit vector. -/
theorem norm_powerIterate_of_ne_zero (h : (A ^ k) x₀ ≠ 0) : ‖powerIterate A x₀ k‖ = 1 := by
  rw [powerIterate, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem norm_powerIterate_le_one : ‖powerIterate A x₀ k‖ ≤ 1 := by
  rcases eq_or_ne ((A ^ k) x₀) 0 with h | h
  · simp [(powerIterate_eq_zero_iff A x₀ k).mpr h]
  · exact (norm_powerIterate_of_ne_zero A x₀ k h).le

/-- Rescaling `x₀` by a scalar multiplies every iterate by that scalar's phase. -/
theorem powerIterate_smul (c : 𝕜) :
    powerIterate A (c • x₀) k = ((‖c‖ : 𝕜)⁻¹ * c) • powerIterate A x₀ k := by
  rw [powerIterate, powerIterate, map_smul, norm_smul, smul_smul, smul_smul]
  push_cast
  rw [mul_inv]
  congr 1
  ring

/-- The power iteration is unchanged by a positive rescaling of the starting vector. -/
theorem powerIterate_ofReal_smul {c : ℝ} (hc : 0 < c) :
    powerIterate A ((c : 𝕜) • x₀) k = powerIterate A x₀ k := by
  rw [powerIterate_smul, RCLike.norm_ofReal, abs_of_pos hc,
    inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr hc.ne'), one_smul]

/-- `powerIterate` satisfies the normalize-at-every-step recurrence on the nose: no positive
scalar is left over, because the normalization divides by a norm rather than by a coordinate. -/
theorem powerIterate_succ :
    powerIterate A x₀ (k + 1) =
      (‖A (powerIterate A x₀ k)‖ : 𝕜)⁻¹ • A (powerIterate A x₀ k) := by
  have hA : A ((A ^ k) x₀) = (A ^ (k + 1)) x₀ := by rw [pow_succ', Module.End.mul_apply]
  rcases eq_or_ne ((A ^ k) x₀) 0 with h | h
  · have h1 : (A ^ (k + 1)) x₀ = 0 := by rw [← hA, h, map_zero]
    simp [powerIterate, h, h1]
  · have ht : (0 : ℝ) < ‖(A ^ k) x₀‖ := norm_pos_iff.mpr h
    have hx : A (powerIterate A x₀ k) = (‖(A ^ k) x₀‖ : 𝕜)⁻¹ • (A ^ (k + 1)) x₀ := by
      rw [powerIterate, map_smul, hA]
    rw [hx, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos ht, smul_smul, powerIterate]
    congr 1
    have hne : (‖(A ^ k) x₀‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr ht.ne'
    push_cast
    field_simp

/-- A sequence that starts at the normalization of `x₀` and normalizes after every application of
`A` *is* the power iteration: the closed form is the specification of the algorithm. -/
theorem eq_powerIterate_of_recurrence {y : ℕ → E} (h0 : y 0 = (‖x₀‖ : 𝕜)⁻¹ • x₀)
    (hs : ∀ j, y (j + 1) = (‖A (y j)‖ : 𝕜)⁻¹ • A (y j)) (j : ℕ) :
    y j = powerIterate A x₀ j := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [hs j, ih, ← powerIterate_succ]

/-! ### Geometric decay off the dominant eigenvector

The subspace of vectors whose `A`-orbit is `O(r^k)` contains every generalized eigenspace with
eigenvalue of modulus below `r`, hence their supremum. -/

variable {A x₀}

/-- The vectors whose `A`-orbit grows no faster than `r^k`. -/
private def geomBounded (A : Module.End 𝕜 E) (r : ℝ) : Submodule 𝕜 E where
  carrier := {w | ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k}
  add_mem' := by
    rintro v w ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    refine ⟨C₁ + C₂, fun k => ?_⟩
    calc ‖(A ^ k) (v + w)‖ ≤ ‖(A ^ k) v‖ + ‖(A ^ k) w‖ := by rw [map_add]; exact norm_add_le _ _
      _ ≤ C₁ * r ^ k + C₂ * r ^ k := add_le_add (h₁ k) (h₂ k)
      _ = (C₁ + C₂) * r ^ k := by ring
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c w ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun k => ?_⟩
    calc ‖(A ^ k) (c • w)‖ = ‖c‖ * ‖(A ^ k) w‖ := by rw [map_smul, norm_smul]
      _ ≤ ‖c‖ * (C * r ^ k) := by gcongr; exact hC k
      _ = ‖c‖ * C * r ^ k := by ring

/-- The decay estimate in the form the induction on `N` needs. -/
private theorem exists_norm_pow_apply_le_of_pow_sub_smul_eq_zero {μ : 𝕜} {r : ℝ} (hr : ‖μ‖ < r)
    (N : ℕ) (w : E) (hw : ((A - μ • (1 : Module.End 𝕜 E)) ^ N) w = 0) :
    ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k := by
  induction N generalizing w with
  | zero => exact ⟨0, by simp_all⟩
  | succ N ih =>
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (norm_nonneg μ) hr
    have hgap : (0 : ℝ) < r - ‖μ‖ := sub_pos.mpr hr
    rw [pow_succ, Module.End.mul_apply] at hw
    obtain ⟨C, hC⟩ := ih _ hw
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC 0)
    have hAw : A w = μ • w + (A - μ • (1 : Module.End 𝕜 E)) w := by
      simp [LinearMap.sub_apply, LinearMap.smul_apply]
    set D : ℝ := ‖w‖ + C / (r - ‖μ‖) with hD
    have hDw : ‖w‖ ≤ D := le_add_of_nonneg_right (div_nonneg hC0 hgap.le)
    have hDgap : C ≤ D * (r - ‖μ‖) := by
      rw [hD, add_mul, div_mul_cancel₀ _ hgap.ne']
      nlinarith [norm_nonneg w]
    refine ⟨D, fun k => ?_⟩
    induction k with
    | zero => simpa using hDw
    | succ k ihk =>
      have hrk : (0 : ℝ) < r ^ k := pow_pos hr0 k
      have hstep : ‖(A ^ (k + 1)) w‖ ≤ ‖μ‖ * ‖(A ^ k) w‖ + C * r ^ k := by
        rw [pow_succ, Module.End.mul_apply, hAw, map_add, map_smul]
        calc ‖μ • (A ^ k) w + (A ^ k) ((A - μ • (1 : Module.End 𝕜 E)) w)‖
            ≤ ‖μ • (A ^ k) w‖ + ‖(A ^ k) ((A - μ • (1 : Module.End 𝕜 E)) w)‖ := norm_add_le _ _
          _ ≤ ‖μ‖ * ‖(A ^ k) w‖ + C * r ^ k := by rw [norm_smul]; gcongr; exact hC k
      have hmul : ‖μ‖ * (D * r ^ k) + C * r ^ k ≤ D * r ^ (k + 1) := by
        have : (‖μ‖ * D + C) * r ^ k ≤ (D * r) * r ^ k := by
          gcongr
          nlinarith
        rw [pow_succ]
        nlinarith
      refine hstep.trans (le_trans ?_ hmul)
      gcongr

/-- **The decay estimate.** A generalized eigenvector of `A` for `μ` has `‖A^k w‖ = O(r^k)` for
every `r > ‖μ‖`; the excess `r - ‖μ‖` is what pays for the polynomial factor a Jordan block of
`μ` would contribute.

The proof is an induction on the index `N` with `(A - μ)^N w = 0`: writing `v = (A - μ) w`, the
orbit obeys `A^{k+1} w = μ A^k w + A^k v`, so a bound `‖A^k v‖ ≤ C r^k` propagates to
`‖A^k w‖ ≤ (‖w‖ + C/(r - ‖μ‖)) r^k`. Neither continuity of `A` nor completeness of `E` is used,
and the spectrum of a restriction of `A` is never computed. -/
theorem exists_norm_pow_apply_le_of_mem_maxGenEigenspace {μ : 𝕜} {w : E} {r : ℝ}
    (hw : w ∈ A.maxGenEigenspace μ) (hr : ‖μ‖ < r) : ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k := by
  obtain ⟨N, hN⟩ := (Module.End.mem_maxGenEigenspace A μ w).mp hw
  exact exists_norm_pow_apply_le_of_pow_sub_smul_eq_zero hr N w hN

/-- Geometric decay on a supremum of maximal generalized eigenspaces: the rate `r` only has to
beat the eigenvalues that actually occur. -/
theorem exists_norm_pow_apply_le_of_mem_iSup {p : 𝕜 → Prop} {w : E} {r : ℝ}
    (hw : w ∈ ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ)
    (hr : ∀ μ, p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k := by
  have key : (⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ) ≤ geomBounded A r := by
    refine iSup₂_le fun μ hμ => ?_
    rcases eq_or_ne (A.maxGenEigenspace μ) ⊥ with h | h
    · rw [h]; exact bot_le
    · exact fun x hx => exists_norm_pow_apply_le_of_mem_maxGenEigenspace hx
        (hr μ hμ (Module.End.HasUnifEigenvalue.lt zero_lt_one h))
  exact key hw

/-- The vectors whose `A`-orbit is negligible after scaling by `l^k`. -/
private def tendstoZero (A : Module.End 𝕜 E) (l : 𝕜) : Submodule 𝕜 E where
  carrier := {v | Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) v) atTop (𝓝 0)}
  add_mem' := by
    intro v v' hv hv'
    have h : Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) v + (l ^ k)⁻¹ • (A ^ k) v') atTop
        (𝓝 ((0 : E) + 0)) := Filter.Tendsto.add hv hv'
    rw [add_zero] at h
    exact h.congr fun k => by rw [map_add, smul_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    have h : Tendsto (fun k => c • ((l ^ k)⁻¹ • (A ^ k) v)) atTop (𝓝 (c • (0 : E))) :=
      Filter.Tendsto.const_smul hv c
    rw [smul_zero] at h
    exact h.congr fun k => by rw [map_smul, smul_comm]

private theorem mem_tendstoZero {l : 𝕜} {v : E} :
    v ∈ tendstoZero A l ↔ Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) v) atTop (𝓝 0) := Iff.rfl

/-- A geometric bound on the orbit becomes a geometric bound at rate `r/‖l‖` after scaling. -/
private theorem norm_inv_pow_smul_pow_apply_le {l : 𝕜} {x : E} {C r : ℝ} (hl : l ≠ 0)
    (hC : ∀ k, ‖(A ^ k) x‖ ≤ C * r ^ k) (k : ℕ) :
    ‖(l ^ k)⁻¹ • (A ^ k) x‖ ≤ C * (r / ‖l‖) ^ k := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  calc ‖(l ^ k)⁻¹ • (A ^ k) x‖ = (‖l‖ ^ k)⁻¹ * ‖(A ^ k) x‖ := by
        rw [norm_smul, norm_inv, norm_pow]
    _ ≤ (‖l‖ ^ k)⁻¹ * (C * r ^ k) := by gcongr; exact hC k
    _ = C * (r / ‖l‖) ^ k := by rw [div_pow]; ring

private theorem tendsto_inv_pow_smul_pow_apply_of_norm_le {l : 𝕜} {x : E} {C r : ℝ} (hl : l ≠ 0)
    (hr0 : 0 ≤ r) (hrl : r < ‖l‖) (hC : ∀ k, ‖(A ^ k) x‖ ≤ C * r ^ k) :
    Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x) atTop (𝓝 0) := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  have hbound : Tendsto (fun k : ℕ => C * (r / ‖l‖) ^ k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (r / ‖l‖) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr0 hl0.le) ((div_lt_one hl0).mpr hrl)
    simpa using h1.const_mul C
  exact squeeze_zero_norm (norm_inv_pow_smul_pow_apply_le hl hC) hbound

/-- Geometric decay after scaling by `l^k`, at a rate chosen for the single eigenvalue `μ`. -/
private theorem mem_tendstoZero_of_mem_maxGenEigenspace {l μ : 𝕜} {x : E}
    (hx : x ∈ A.maxGenEigenspace μ) (hl : l ≠ 0) (hμl : ‖μ‖ < ‖l‖) : x ∈ tendstoZero A l := by
  have hμr : ‖μ‖ < (‖μ‖ + ‖l‖) / 2 := by linarith
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_maxGenEigenspace hx hμr
  exact mem_tendstoZero.mpr (tendsto_inv_pow_smul_pow_apply_of_norm_le hl
    (le_trans (norm_nonneg μ) hμr.le) (by linarith) hC)

/-- The subdominant part of the orbit is negligible after scaling by `λ^k`: this is the only
analytic input to the convergence theorem, and it holds under the strict dominance `‖μ‖ < ‖λ‖`
with no uniform gap. -/
theorem tendsto_inv_pow_smul_pow_apply_of_mem_iSup {l : 𝕜} {w : E} (hl : l ≠ 0)
    (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖) :
    Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) w) atTop (𝓝 0) := by
  have key : (⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ) ≤ tendstoZero A l := by
    refine iSup₂_le fun μ hμ => ?_
    rcases eq_or_ne (A.maxGenEigenspace μ) ⊥ with h | h
    · rw [h]; exact bot_le
    · exact fun x hx => mem_tendstoZero_of_mem_maxGenEigenspace hx hl
        (hdom μ hμ (Module.End.HasUnifEigenvalue.lt zero_lt_one h))
  exact mem_tendstoZero.mp (key hw)

/-! ### Convergence of the power method -/

variable {l : 𝕜} {u w : E} {C r : ℝ}

private theorem pow_apply_of_apply_eq_smul (hu : A u = l • u) (k : ℕ) :
    (A ^ k) u = l ^ k • u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hu, smul_smul, ← pow_succ]

private theorem inv_pow_smul_pow_apply_add (hl : l ≠ 0) (hu : A u = l • u) (k : ℕ) :
    (l ^ k)⁻¹ • (A ^ k) (u + w) = u + (l ^ k)⁻¹ • (A ^ k) w := by
  rw [map_add, pow_apply_of_apply_eq_smul hu, smul_add, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero k hl), one_smul]

/-- The error of the scaled power iterate is `O((r/‖λ‖)^k)` whenever the subdominant part `w`
obeys `‖A^k w‖ ≤ C r^k`. -/
theorem norm_inv_pow_smul_pow_apply_sub_le (hl : l ≠ 0) (hu : A u = l • u)
    (hw : ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k) (k : ℕ) :
    ‖(l ^ k)⁻¹ • (A ^ k) (u + w) - u‖ ≤ C * (r / ‖l‖) ^ k := by
  rw [inv_pow_smul_pow_apply_add hl hu, add_sub_cancel_left]
  exact norm_inv_pow_smul_pow_apply_le hl hw k

/-- **Convergence of the power method.** If the starting vector splits as `x₀ = u + w` with `u`
an eigenvector for `λ` and `w` in the span of the other generalized eigenspaces, and every other
eigenvalue has strictly smaller modulus, then `λ^{-k} A^k x₀ → u`.

The limit `u` is the component of `x₀` in the `λ`-generalized eigenspace, so this is the
statement that `λ^{-k} A^k x₀` converges to the spectral projection of `x₀`; the splitting is
unique by `Krylov.eq_of_add_eq_add_mem_maxGenEigenspace`. -/
theorem powerIterate_tendsto {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u)
    (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x₀) atTop (𝓝 u) := by
  subst hx₀
  have h := tendsto_inv_pow_smul_pow_apply_of_mem_iSup hl hw hdom
  have : Tendsto (fun k => u + (l ^ k)⁻¹ • (A ^ k) w) atTop (𝓝 (u + 0)) :=
    tendsto_const_nhds.add h
  simpa only [inv_pow_smul_pow_apply_add hl hu, add_zero] using this

/-- The geometric rate: for every `r` above the moduli of the subdominant eigenvalues, the error
of `λ^{-k} A^k x₀` is `O((r/‖λ‖)^k)`. -/
theorem exists_norm_inv_pow_smul_pow_apply_sub_le {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u)
    (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hr : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < r) (hx₀ : x₀ = u + w) :
    ∃ C : ℝ, ∀ k, ‖(l ^ k)⁻¹ • (A ^ k) x₀ - u‖ ≤ C * (r / ‖l‖) ^ k := by
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_iSup hw hr
  exact ⟨C, fun k => hx₀ ▸ norm_inv_pow_smul_pow_apply_sub_le hl hu hC k⟩

/-! ### The normalized iterate

`powerIterate` itself converges only up to the unimodular factor `(λ/‖λ‖)^k`, which the two
statements below handle in the two available ways: divide it out, or measure the eigenvalue
residual, which does not see it. -/

private theorem norm_ofReal_norm_div_pow (hl : l ≠ 0) (k : ℕ) :
    ‖(((‖l‖ : 𝕜) / l) ^ k)‖ = 1 := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  rw [norm_pow, norm_div, RCLike.norm_ofReal, abs_of_pos hl0, div_self hl0.ne', one_pow]

/-- Convergence of the normalized power iterate, after dividing out the unimodular factor
`(λ/‖λ‖)^k`: the limit is the normalized eigenvector `‖u‖⁻¹ • u`. -/
theorem tendsto_smul_powerIterate {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k) atTop
      (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  have hlk : ∀ k : ℕ, (l ^ k) ≠ 0 := fun k => pow_ne_zero k hl
  set z : ℕ → E := fun k => (l ^ k)⁻¹ • (A ^ k) x₀ with hz
  have hzt : Tendsto z atTop (𝓝 u) := powerIterate_tendsto hl hu hw hdom hx₀
  have hApp : ∀ k, (A ^ k) x₀ = l ^ k • z k := fun k => by
    rw [hz]; rw [smul_smul, mul_inv_cancel₀ (hlk k), one_smul]
  have heq : ∀ k, (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k = (‖z k‖ : 𝕜)⁻¹ • z k := by
    intro k
    rw [powerIterate, hApp k, norm_smul, norm_pow, smul_smul, smul_smul]
    congr 1
    have h1 : ((‖l‖ : 𝕜)) ≠ 0 := RCLike.ofReal_ne_zero.mpr hl0.ne'
    push_cast
    rw [div_pow]
    field_simp
  have hnorm : Tendsto (fun k => ((‖z k‖ : 𝕜))⁻¹) atTop (𝓝 ((‖u‖ : 𝕜)⁻¹)) := by
    refine Tendsto.inv₀ ?_ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu0))
    exact (RCLike.continuous_ofReal.tendsto _).comp hzt.norm
  simpa only [heq] using hnorm.smul hzt

/-- **Essential convergence** of the normalized power iterates, in the sense of Saad,
*Large Eigenvalue Problems*, §5.1: there is a sequence of scalars of modulus one whose products
with the iterates converge to the normalized eigenvector.
`Krylov.tendsto_smul_powerIterate` is the same statement with the sequence named. -/
theorem exists_norm_eq_one_tendsto_smul_powerIterate {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u)
    (hu0 : u ≠ 0) (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖) (hx₀ : x₀ = u + w) :
    ∃ c : ℕ → 𝕜, (∀ k, ‖c k‖ = 1) ∧
      Tendsto (fun k => c k • powerIterate A x₀ k) atTop (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) :=
  ⟨fun k => ((‖l‖ : 𝕜) / l) ^ k, norm_ofReal_norm_div_pow hl,
    tendsto_smul_powerIterate hl hu hu0 hw hdom hx₀⟩

/-- The phase-free statement: the eigenvalue residual of the normalized power iterate tends to
zero, so `x_k` becomes an approximate eigenvector for `λ`. -/
theorem tendsto_norm_sub_smul_powerIterate {x₀ : E} (hA : Continuous A) (hl : l ≠ 0)
    (hu : A u = l • u) (hu0 : u ≠ 0) (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => ‖A (powerIterate A x₀ k) - l • powerIterate A x₀ k‖) atTop (𝓝 0) := by
  have hres : Continuous fun v : E => A v - l • v := hA.sub (continuous_const_smul l)
  have hlim := (hres.tendsto _).comp (tendsto_smul_powerIterate hl hu hu0 hw hdom hx₀)
  have hzero : A ((‖u‖ : 𝕜)⁻¹ • u) - l • (‖u‖ : 𝕜)⁻¹ • u = 0 := by
    rw [map_smul, hu, smul_comm, sub_self]
  rw [Function.comp_def, hzero] at hlim
  have heq : ∀ k, ‖A (powerIterate A x₀ k) - l • powerIterate A x₀ k‖ =
      ‖A ((((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k) -
        l • (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k‖ := by
    intro k
    rw [map_smul, smul_comm l, ← smul_sub, norm_smul, norm_ofReal_norm_div_pow hl, one_mul]
  simpa only [heq, norm_zero] using hlim.norm

/-! ### The splitting of the starting vector

Over an algebraically closed field and in finite dimension the generalized eigenspaces span, so
every `x₀` splits as required, uniquely. -/

section Splitting

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **The spectral splitting of a set of eigenvalues.** The span of the generalized eigenspaces
whose eigenvalue satisfies `p` and the span of all the others are complementary.

This is the source of the spectral projector `Krylov.spectralProjector` onto the first summand:
it is `Submodule.projection` applied to this decomposition, which is an *oblique* projector, not
an orthogonal one, unless `B` is normal. Disjointness is the independence of the generalized
eigenspaces, split along the two halves of `p`; codisjointness is `iSup_split` together with the
fact that over an algebraically closed field in finite dimension the generalized eigenspaces
span. -/
theorem isCompl_iSup_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    (B : Module.End K V) (p : K → Prop) :
    IsCompl (⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ)
      (⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ) where
  disjoint := (B.independent_maxGenEigenspace).disjoint_biSup_biSup
    (s := {μ | p μ}) (t := {μ | ¬ p μ}) (Set.disjoint_left.mpr fun _ ha ha' => ha' ha)
  codisjoint := by
    rw [codisjoint_iff, ← iSup_split (B.maxGenEigenspace) p, B.iSup_maxGenEigenspace_eq_top]

/-- The `l`-generalized eigenspace and the span of the other generalized eigenspaces are
complementary: the one-eigenvalue case of `Krylov.isCompl_iSup_maxGenEigenspace`, which is what
the power method's splitting `x₀ = u + w` uses. -/
theorem isCompl_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V] (B : Module.End K V)
    (l : K) : IsCompl (B.maxGenEigenspace l) (⨆ μ, ⨆ _ : μ ≠ l, B.maxGenEigenspace μ) := by
  have h := isCompl_iSup_maxGenEigenspace B (· = l)
  rwa [iSup_iSup_eq_left] at h

/-- The generalized-eigenspace splitting `x = u + w` with `u` in the `l`-generalized eigenspace
and `w` in the span of the others. -/
theorem exists_eq_add_mem_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    (B : Module.End K V) (l : K) (x : V) :
    ∃ u ∈ B.maxGenEigenspace l, ∃ w ∈ ⨆ μ, ⨆ _ : μ ≠ l, B.maxGenEigenspace μ, x = u + w := by
  have htop := codisjoint_iff.mp (isCompl_maxGenEigenspace B l).codisjoint
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (htop.ge (Submodule.mem_top (x := x)))
  exact ⟨u, hu, w, hw, huw.symm⟩

/-- The splitting is unique, which is what makes the limit in `Krylov.powerIterate_tendsto` a
function of `x₀` alone — the spectral projection of `x₀` onto the `l`-generalized eigenspace. -/
theorem eq_of_add_eq_add_mem_maxGenEigenspace {B : Module.End K V} {l : K} {u u' w w' : V}
    (hu : u ∈ B.maxGenEigenspace l) (hu' : u' ∈ B.maxGenEigenspace l)
    (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, B.maxGenEigenspace μ)
    (hw' : w' ∈ ⨆ μ, ⨆ _ : μ ≠ l, B.maxGenEigenspace μ) (h : u + w = u' + w') :
    u = u' ∧ w = w' := by
  have hdisj := B.independent_maxGenEigenspace l
  have hmem : u - u' ∈ B.maxGenEigenspace l ⊓ ⨆ μ, ⨆ _ : μ ≠ l, B.maxGenEigenspace μ := by
    refine ⟨sub_mem hu hu', ?_⟩
    have : u - u' = w' - w := by linear_combination (norm := module) h
    rw [this]
    exact sub_mem hw' hw
  rw [disjoint_iff.mp hdisj] at hmem
  have h1 : u = u' := sub_eq_zero.mp (Submodule.mem_bot K |>.mp hmem)
  exact ⟨h1, by rw [h1] at h; exact add_left_cancel h⟩

/-- A simple eigenvalue is semi-simple: if the maximal generalized eigenspace of `l` is a line,
it is the eigenspace, so every generalized eigenvector for `l` is an eigenvector. -/
theorem maxGenEigenspace_eq_eigenspace_of_finrank_eq_one {B : Module.End K V} {l : K}
    (h : Module.finrank K (B.maxGenEigenspace l) = 1) :
    B.maxGenEigenspace l = B.eigenspace l := by
  have hfin : FiniteDimensional K (B.maxGenEigenspace l) :=
    Module.finite_of_finrank_pos (by omega)
  have hne : B.maxGenEigenspace l ≠ ⊥ := fun hbot => by
    rw [hbot] at h; simp at h
  have hev : B.HasEigenvalue l := Module.End.HasUnifEigenvalue.lt zero_lt_one hne
  have hle : B.eigenspace l ≤ B.maxGenEigenspace l := Module.End.eigenspace_le_maxGenEigenspace
  have : FiniteDimensional K (B.eigenspace l) := Submodule.finiteDimensional_of_le hle
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [h]
  exact Submodule.one_le_finrank_iff.mpr (Module.End.hasEigenvalue_iff.mp hev)

/-! ### The spectral projector of a set of eigenvalues

The projector along the splitting above, together with the two facts a subspace-iteration bound
needs about it: which vectors it kills, and when it is injective on a starting subspace. -/

section SpectralProjector

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- **The spectral projector** of the set of eigenvalues picked out by `p`: the projection onto
`⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ` along the span of the remaining generalized eigenspaces.

It is *oblique* — `Submodule.starProjection` is a different map unless `B` is normal — and it is
the `P` of the subspace-iteration bound of Saad, *Numerical Methods for Large Eigenvalue
Problems*, Thm 5.2, where `p` selects the `m` dominant eigenvalues. Taking `p` to be `(· = l)`
recovers the projector onto a single generalized eigenspace. -/
noncomputable def spectralProjector (B : Module.End K V) (p : K → Prop) : Module.End K V :=
  Submodule.projection _ _ (isCompl_iSup_maxGenEigenspace B p)

variable {B : Module.End K V} {p : K → Prop}

/-- The projector lands in the invariant subspace of the selected eigenvalues. -/
@[simp]
theorem spectralProjector_apply_mem (x : V) :
    spectralProjector B p x ∈ ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ :=
  Submodule.projection_apply_mem _ _

/-- The complementary part of `x` lies in the invariant subspace of the discarded eigenvalues.
This is the step that feeds `Krylov.exists_norm_pow_apply_le_of_mem_iSup`. -/
theorem sub_spectralProjector_mem (x : V) :
    x - spectralProjector B p x ∈ ⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ :=
  Submodule.sub_projection_mem _ _

/-- The projector fixes the invariant subspace it projects onto. -/
theorem spectralProjector_apply_of_mem {x : V}
    (hx : x ∈ ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ) : spectralProjector B p x = x :=
  Submodule.projection_apply_of_mem_left _ hx

/-- The projector kills exactly the invariant subspace of the discarded eigenvalues. -/
@[simp]
theorem spectralProjector_apply_eq_zero_iff {x : V} :
    spectralProjector B p x = 0 ↔ x ∈ ⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ :=
  Submodule.projection_apply_eq_zero_iff _

/-- The kernel of the spectral projector is the invariant subspace of the discarded
eigenvalues. -/
theorem ker_spectralProjector :
    LinearMap.ker (spectralProjector B p) = ⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ :=
  Submodule.ker_projection _

/-- The range of the spectral projector is the invariant subspace of the selected eigenvalues. -/
theorem range_spectralProjector :
    LinearMap.range (spectralProjector B p) = ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ :=
  Submodule.range_projection _

/-- A projector is idempotent. -/
theorem isIdempotentElem_spectralProjector : IsIdempotentElem (spectralProjector B p) :=
  Submodule.isIdempotentElem_projection _

/-- The projector reads off the first summand of the spectral splitting. -/
theorem spectralProjector_add_of_mem {u w : V}
    (hu : u ∈ ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ)
    (hw : w ∈ ⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ) :
    spectralProjector B p (u + w) = u := by
  rw [map_add, spectralProjector_apply_of_mem hu, spectralProjector_apply_eq_zero_iff.mpr hw,
    add_zero]

/-- The spectral projector is injective on a subspace exactly when that subspace meets the
invariant subspace of the discarded eigenvalues only in `0`. Saad, *Numerical Methods for Large
Eigenvalue Problems*, Thm 5.2 states its hypothesis as the linear independence of the images
`P x₁, …, P x_m` of a spanning family of `S`, which is this disjointness. -/
theorem injOn_spectralProjector_iff {S : Submodule K V} :
    Set.InjOn (spectralProjector B p) S ↔
      Disjoint S (⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ) := by
  refine ⟨fun h => disjoint_iff_inf_le.mpr fun x hx => ?_, fun h => ?_⟩
  · have h0 : spectralProjector B p x = 0 := spectralProjector_apply_eq_zero_iff.mpr hx.2
    simpa using h hx.1 (Submodule.zero_mem S) (by simpa using h0)
  · refine LinearMap.injOn_of_disjoint_ker (le_refl (S : Set V)) ?_
    rwa [ker_spectralProjector]

/-- **The starting subspace has a unique preimage for each dominant vector.** If the spectral
projector is injective on `S` and `S` has the dimension of the invariant subspace it projects
onto, then every `u` of that invariant subspace is `P s` for exactly one `s ∈ S`.

Injectivity makes `P` a bijection from `S` onto its image by rank–nullity, and the equality of
dimensions promotes the image to the whole invariant subspace. This is the first half of the
conclusion of Saad, *Numerical Methods for Large Eigenvalue Problems*, Thm 5.2, and the vector
`s` it produces is the one the bound's constant is measured against. -/
theorem existsUnique_mem_spectralProjector_eq {S : Submodule K V}
    (hdisj : Disjoint S (⨆ μ, ⨆ _ : ¬ p μ, B.maxGenEigenspace μ))
    (hrank : Module.finrank K S = Module.finrank K ↥(⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ))
    {u : V} (hu : u ∈ ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ) :
    ∃! s : V, s ∈ S ∧ spectralProjector B p s = u := by
  have hinj : Set.InjOn (spectralProjector B p) S := injOn_spectralProjector_iff.mpr hdisj
  have hker : LinearMap.ker (spectralProjector B p ∘ₗ S.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hx0
    simpa using hinj hx (Submodule.zero_mem S) (by simpa using hx0)
  have hrange : LinearMap.range (spectralProjector B p ∘ₗ S.subtype) =
      S.map (spectralProjector B p) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hfin : Module.finrank K ↥(S.map (spectralProjector B p)) = Module.finrank K S := by
    have h := (spectralProjector B p ∘ₗ S.subtype).finrank_range_add_finrank_ker
    rw [hker, hrange] at h
    simpa using h
  have hle : S.map (spectralProjector B p) ≤ ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ := by
    rw [← range_spectralProjector (B := B) (p := p)]
    exact LinearMap.map_le_range
  have heq : S.map (spectralProjector B p) = ⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hfin, hrank])
  obtain ⟨s, hs, hsu⟩ := Submodule.mem_map.mp (heq.ge hu)
  refine ⟨s, ⟨hs, hsu⟩, ?_⟩
  rintro y ⟨hy, hyu⟩
  exact hinj hy hs (by rw [hyu, hsu])

end SpectralProjector

end Splitting

/-- The packaged form of the convergence theorem, at the hypotheses under which it is usually
stated: over an algebraically closed field, in finite dimension, with `l` a nonzero **semi-simple**
eigenvalue of strictly largest modulus, *every* starting vector splits as `x₀ = u + w` with `u` an
eigenvector for `l`, and `l^{-k} A^k x₀ → u`. The power method converges from every `x₀` whose
component `u` is nonzero, and the exceptional set is the hyperplane `u = 0`. -/
theorem exists_eq_add_tendsto [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] (hl : l ≠ 0)
    (hss : A.maxGenEigenspace l = A.eigenspace l)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖) (x₀ : E) :
    ∃ u w, A u = l • u ∧ w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ ∧ x₀ = u + w ∧
      Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x₀) atTop (𝓝 u) := by
  obtain ⟨u, hu, w, hw, huw⟩ := exists_eq_add_mem_maxGenEigenspace A l x₀
  rw [hss, Module.End.mem_eigenspace_iff] at hu
  exact ⟨u, w, hu, hw, huw, powerIterate_tendsto hl hu hw hdom huw⟩

/-! ### Inverse iteration

Shift and invert: the power method run on `(A - σ)⁻¹`, whose eigenvalues are the `(μ - σ)⁻¹`, so
that the eigenvalue of `A` *closest to the shift* is the dominant one. -/

section InverseIteration

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Inverse iteration** (shift-and-invert power method) with shift `σ`: the power iteration of
the inverse of the shifted operator `A - σ`.

The inverse is `Ring.inverse`, so the definition is total: at a shift belonging to the spectrum
the shifted operator is not invertible, `Ring.inverse` returns `0`, and the iteration is the power
iteration of `0`. Every statement about convergence assumes `IsUnit (A - σ)`, which in finite
dimension is exactly `σ ∉ spectrum 𝕜 A`. -/
noncomputable def inverseIterate (A : Module.End 𝕜 E) (σ : 𝕜) (x₀ : E) (k : ℕ) : E :=
  powerIterate (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))) x₀ k

/-- Inverse iteration is the power method applied to the inverse of the shifted operator. -/
@[simp]
theorem inverseIterate_eq_powerIterate (A : Module.End 𝕜 E) (σ : 𝕜) (x₀ : E) (k : ℕ) :
    inverseIterate A σ x₀ k
      = powerIterate (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))) x₀ k := rfl

variable {A : Module.End 𝕜 E} {σ : 𝕜}

private theorem sub_smul_one_apply (μ : 𝕜) (x : E) :
    (A - μ • (1 : Module.End 𝕜 E)) x = A x - μ • x := by
  simp

private theorem eq_zero_of_isUnit_apply_eq_zero {M : Module.End 𝕜 E} (hM : IsUnit M) {y : E}
    (hy : M y = 0) : y = 0 := by
  obtain ⟨v, rfl⟩ := hM
  have h : ((v⁻¹ : (Module.End 𝕜 E)ˣ) : Module.End 𝕜 E) ((v : Module.End 𝕜 E) y) = y := by
    rw [← Module.End.mul_apply, v.inv_mul, Module.End.one_apply]
  rw [hy, map_zero] at h
  exact h.symm

private theorem commute_inverse_sub_smul_one
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (μ : 𝕜) :
    Commute (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))) (A - μ • (1 : Module.End 𝕜 E)) := by
  have hT : Commute (Ring.inverse (A - σ • (1 : Module.End 𝕜 E)))
      (A - σ • (1 : Module.End 𝕜 E)) :=
    (Ring.inverse_mul_cancel _ hσ).trans (Ring.mul_inverse_cancel _ hσ).symm
  have hone := (Commute.one_right (Ring.inverse (A - σ • (1 : Module.End 𝕜 E)))).smul_right (μ - σ)
  have := hT.sub_right hone
  have heq : A - σ • (1 : Module.End 𝕜 E) - (μ - σ) • (1 : Module.End 𝕜 E)
      = A - μ • (1 : Module.End 𝕜 E) := by module
  rwa [heq] at this

/-- **The eigenvectors are unchanged and the eigenvalues are inverted.** An eigenvector of `A`
for an eigenvalue `μ` other than the shift is an eigenvector of the shifted inverse for
`(μ - σ)⁻¹`. -/
theorem inverse_apply_eq_smul {μ : 𝕜} {x : E} (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E)))
    (hμ : μ ≠ σ) (hx : A x = μ • x) :
    Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) x = (μ - σ)⁻¹ • x := by
  have hT : (A - σ • (1 : Module.End 𝕜 E)) x = (μ - σ) • x := by
    rw [sub_smul_one_apply, hx, sub_smul]
  have h := congrArg (fun f : Module.End 𝕜 E => f x) (Ring.inverse_mul_cancel _ hσ)
  simp only [Module.End.mul_apply, Module.End.one_apply, hT, map_smul] at h
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hμ), one_smul]

/-- Nothing generalized survives at the shift: the shifted operator is invertible there. -/
theorem maxGenEigenspace_eq_bot_of_isUnit (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) :
    A.maxGenEigenspace σ = ⊥ := by
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨N, hN⟩ := (Module.End.mem_maxGenEigenspace A σ x).1 hx
  exact Submodule.mem_bot _ |>.2 (eq_zero_of_isUnit_apply_eq_zero (hσ.pow N) hN)

/-- The generalized eigenspaces are carried along too: a generalized eigenvector of `A` for
`μ ≠ σ` is a generalized eigenvector of the shifted inverse for `(μ - σ)⁻¹`, of the same index. -/
theorem maxGenEigenspace_le_maxGenEigenspace_inverse {μ : 𝕜}
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (hμ : μ ≠ σ) :
    A.maxGenEigenspace μ ≤
      (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))).maxGenEigenspace (μ - σ)⁻¹ := by
  have hμσ : μ - σ ≠ 0 := sub_ne_zero.2 hμ
  have hkey : Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) - (μ - σ)⁻¹ • (1 : Module.End 𝕜 E)
      = (-(μ - σ)⁻¹) •
        (Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) * (A - μ • (1 : Module.End 𝕜 E))) := by
    have heq : A - μ • (1 : Module.End 𝕜 E)
        = (A - σ • (1 : Module.End 𝕜 E)) - (μ - σ) • (1 : Module.End 𝕜 E) := by module
    rw [heq, mul_sub, Ring.inverse_mul_cancel _ hσ, mul_smul_comm, mul_one, smul_sub, smul_smul,
      show (-(μ - σ)⁻¹) * (μ - σ) = -1 by rw [neg_mul, inv_mul_cancel₀ hμσ]]
    module
  intro x hx
  obtain ⟨N, hN⟩ := (Module.End.mem_maxGenEigenspace A μ x).1 hx
  refine (Module.End.mem_maxGenEigenspace _ _ x).2 ⟨N, ?_⟩
  rw [hkey, smul_pow, (commute_inverse_sub_smul_one hσ μ).mul_pow]
  simp [Module.End.mul_apply, hN]

/-- An eigenvalue of the shifted inverse comes from an eigenvalue of `A`: it is nonzero, and
`σ + ν⁻¹` is an eigenvalue of `A`. -/
theorem hasEigenvalue_of_hasEigenvalue_inverse {ν : 𝕜}
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E)))
    (hν : (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))).HasEigenvalue ν) :
    ν ≠ 0 ∧ A.HasEigenvalue (σ + ν⁻¹) := by
  obtain ⟨x, hx, hx0⟩ := hν.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have hround := congrArg (fun f : Module.End 𝕜 E => f x) (Ring.mul_inverse_cancel _ hσ)
  simp only [Module.End.mul_apply, Module.End.one_apply, hx, map_smul] at hround
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hround
    exact hx0 hround.symm
  refine ⟨hν0, Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 ?_, hx0⟩⟩
  have hT : (A - σ • (1 : Module.End 𝕜 E)) x = ν⁻¹ • x := by
    conv_rhs => rw [← hround]
    rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
  rw [sub_smul_one_apply] at hT
  rw [add_smul, ← hT]
  abel

/-- **Convergence of inverse iteration.** If `l` is an eigenvalue of `A` strictly closer to the
shift `σ` than every other eigenvalue, and the starting vector splits as `x₀ = u + w` with `u` an
eigenvector for `l` and `w` in the span of the other generalized eigenspaces, then the iterates
converge essentially — up to the unimodular factor `((l - σ)/‖l - σ‖)^k` — to the normalized
eigenvector `‖u‖⁻¹ u`.

The eigenvalue of the shifted inverse that this exhibits as dominant is `(l - σ)⁻¹`; the rate of
`Krylov.exists_norm_inv_pow_smul_pow_apply_sub_le` reads `(‖l - σ‖/‖μ₂ - σ‖)^k`, so the closer
the shift is to `l` relative to the rest of the spectrum, the faster the convergence. That is
what makes shifting worth its cost, since the dominance hypothesis here is about *distances to
the shift* and not about moduli. -/
theorem tendsto_smul_inverseIterate {l : 𝕜} {u w x₀ : E}
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ ⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ)
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖l - σ‖ < ‖μ - σ‖) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (((l - σ) / (‖l - σ‖ : 𝕜)) ^ k) • inverseIterate A σ x₀ k) atTop
      (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) := by
  set B : Module.End 𝕜 E := Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) with hB
  have hlσ : l ≠ σ := by
    rintro rfl
    refine hu0 (eq_zero_of_isUnit_apply_eq_zero hσ ?_)
    rw [sub_smul_one_apply, hu, sub_self]
  have hlσ0 : l - σ ≠ 0 := sub_ne_zero.2 hlσ
  have hl' : (l - σ)⁻¹ ≠ 0 := inv_ne_zero hlσ0
  have hu' : B u = (l - σ)⁻¹ • u := inverse_apply_eq_smul hσ hlσ hu
  have hw' : w ∈ ⨆ ν, ⨆ _ : ν ≠ (l - σ)⁻¹, B.maxGenEigenspace ν := by
    refine (iSup₂_le fun μ hμ => ?_ : (⨆ μ, ⨆ _ : μ ≠ l, A.maxGenEigenspace μ) ≤ _) hw
    rcases eq_or_ne μ σ with rfl | hμσ
    · rw [maxGenEigenspace_eq_bot_of_isUnit hσ]; exact bot_le
    · refine le_trans (maxGenEigenspace_le_maxGenEigenspace_inverse hσ hμσ) ?_
      exact le_iSup₂ (f := fun ν (_ : ν ≠ (l - σ)⁻¹) => B.maxGenEigenspace ν) _
        (fun h => hμ (by simpa [sub_left_inj] using inv_inj.1 h))
  have hdom' : ∀ ν, ν ≠ (l - σ)⁻¹ → B.HasEigenvalue ν → ‖ν‖ < ‖(l - σ)⁻¹‖ := by
    intro ν hν hνe
    obtain ⟨hν0, hA⟩ := hasEigenvalue_of_hasEigenvalue_inverse hσ hνe
    have hμ : σ + ν⁻¹ ≠ l := by
      rintro rfl
      exact hν (by rw [add_sub_cancel_left, inv_inv])
    have hlt := hdom _ hμ hA
    rw [add_sub_cancel_left, norm_inv] at hlt
    have h1 : (0 : ℝ) < ‖ν‖ := norm_pos_iff.2 hν0
    have h2 : (0 : ℝ) < ‖l - σ‖ := norm_pos_iff.2 hlσ0
    rw [inv_eq_one_div, lt_div_iff₀ h1] at hlt
    rw [norm_inv, inv_eq_one_div, lt_div_iff₀ h2, mul_comm]
    exact hlt
  have hfac : ((‖(l - σ)⁻¹‖ : 𝕜)) / (l - σ)⁻¹ = (l - σ) / (‖l - σ‖ : 𝕜) := by
    rw [norm_inv, RCLike.ofReal_inv, inv_div_inv]
  have hlim := tendsto_smul_powerIterate hl' hu' hu0 hw' hdom' hx₀
  rw [hfac, hB] at hlim
  exact hlim

end InverseIteration

/-! ### Subspace iteration

The block form of the power method: a whole subspace is carried along by `A`, and the dominant
eigenvectors come to lie close to it. The distance is measured with `Submodule.starProjection`,
so this is the one part of the module that needs an inner product. -/

section SubspaceIteration

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (A : Module.End 𝕜 E) (S : Submodule 𝕜 E)

/-- **Simple subspace iteration** in closed form: the subspace spanned by the `k`-th block of
iterates is `A^k S₀`.

The algorithm of Saad, *Numerical Methods for Large Eigenvalue Problems*, Alg. 5.1 (Bauer's
Treppeniteration) reorthonormalizes its block of vectors after every multiplication by `A`, which
replaces the basis but not the subspace it spans; so, exactly as `Krylov.powerIterate` is a
normalization of `A^k x₀`, the subspace produced after `k` steps is this one, whatever
normalization is used. -/
def subspaceIterate (k : ℕ) : Submodule 𝕜 E := S.map (A ^ k)

/-- A block of `m` starting vectors spans a finite-dimensional subspace, and so does every
iterate. This is what supplies the orthogonal projection onto `A^k S₀`, with no completeness
assumption on the ambient space. -/
instance [FiniteDimensional 𝕜 S] (k : ℕ) : FiniteDimensional 𝕜 (subspaceIterate A S k) :=
  inferInstanceAs (FiniteDimensional 𝕜 (S.map (A ^ k)))

variable {A S}

/-- Membership in an iterate: the `k`-th subspace is the image of the starting one. -/
theorem mem_subspaceIterate {k : ℕ} {x : E} :
    x ∈ subspaceIterate A S k ↔ ∃ y ∈ S, (A ^ k) y = x := Submodule.mem_map

/-- The candidate vectors the convergence bound is proved with. -/
theorem apply_pow_mem_subspaceIterate {y : E} (hy : y ∈ S) (k : ℕ) :
    (A ^ k) y ∈ subspaceIterate A S k := Submodule.mem_map_of_mem hy

/-- The iteration starts at the given subspace. -/
@[simp]
theorem subspaceIterate_zero : subspaceIterate A S 0 = S := by
  rw [subspaceIterate, pow_zero, Module.End.one_eq_id, Submodule.map_id]

/-- One step of the iteration is one application of `A` to the subspace, which is the recurrence
the algorithm runs. -/
theorem subspaceIterate_succ (k : ℕ) :
    subspaceIterate A S (k + 1) = (subspaceIterate A S k).map A := by
  rw [subspaceIterate, subspaceIterate, pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]

/-- **The subspace-iteration bound**, in the form the proof actually consumes: no spectrum, no
projector and no finite dimension of the ambient space.

If `u` is an eigenvector of `A` for `λ ≠ 0`, if `s` lies in the starting subspace `S`, and if the
orbit of the discrepancy `s - u` obeys `‖A^k (s - u)‖ ≤ C r^k`, then the distance from `u` to
`A^k S` is at most `C (r/‖λ‖)^k`. The proof exhibits one candidate, `λ^{-k} A^k s`, which lies in
`A^k S` and whose error is exactly `λ^{-k} A^k (s - u)`; the orthogonal projection does at least
as well, being the best approximation from the subspace.

Compare `Krylov.norm_inv_pow_smul_pow_apply_sub_le`, the same estimate for the power method: there
the approximant is the scaled iterate itself, here it is the best approximant from the subspace
that contains it, so the block statement is the sharper of the two. -/
theorem norm_sub_starProjection_subspaceIterate_le [FiniteDimensional 𝕜 S] {u s : E} {l : 𝕜}
    {C r : ℝ} (hl : l ≠ 0) (hu : A u = l • u) (hs : s ∈ S)
    (hC : ∀ k, ‖(A ^ k) (s - u)‖ ≤ C * r ^ k) (k : ℕ) :
    ‖u - (subspaceIterate A S k).starProjection u‖ ≤ C * (r / ‖l‖) ^ k := by
  have hy : (l ^ k)⁻¹ • (A ^ k) s ∈ subspaceIterate A S k :=
    Submodule.smul_mem _ _ (apply_pow_mem_subspaceIterate hs k)
  have key : (l ^ k)⁻¹ • (A ^ k) s = u + (l ^ k)⁻¹ • (A ^ k) (s - u) := by
    have h := inv_pow_smul_pow_apply_add (w := s - u) hl hu k
    rwa [add_sub_cancel] at h
  have heq : ‖u - (l ^ k)⁻¹ • (A ^ k) s‖ = ‖(l ^ k)⁻¹ • (A ^ k) (s - u)‖ := by
    rw [key, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  refine ((isBestApprox_starProjection _ u).2 _ hy).trans ?_
  rw [heq]
  exact norm_inv_pow_smul_pow_apply_le hl hC k

/-- **Convergence of subspace iteration** (Saad, *Numerical Methods for Large Eigenvalue
Problems*, Thm 5.2).

Let a predicate `p` select a set of eigenvalues, let `M` be the span of their generalized
eigenspaces and `W` the span of the rest. If the spectral projector is injective on the starting
subspace `S` — equivalently, `Disjoint S W`, which is the book's requirement that the projections
of a spanning family of `S` be linearly independent — and `S` has the dimension of `M`, then every
eigenvector `u ∈ M` with eigenvalue `λ ≠ 0` satisfies `‖u - P_{A^k S} u‖ ≤ C (r/‖λ‖)^k`, for every
`r` exceeding the moduli of the unselected eigenvalues.

The bound is informative exactly when `r < ‖λ‖`, that is when the selected eigenvalues dominate;
`Krylov.tendsto_starProjection_subspaceIterate` is that reading. The book states the constant as
`‖u - s‖` and the rate as `(|λ_{m+1}/λ_i| + ε_k)^k` with `ε_k → 0`; the trade made here is the
same one the power method makes, a constant `C` in exchange for an exponent whose base does not
move. -/
theorem exists_norm_sub_starProjection_subspaceIterate_le [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E]
    {p : 𝕜 → Prop} {u : E} {l : 𝕜} {r : ℝ}
    (hdisj : Disjoint S (⨆ μ, ⨆ _ : ¬ p μ, A.maxGenEigenspace μ))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 ↥(⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ))
    (hl : l ≠ 0) (hu : A u = l • u) (hmem : u ∈ ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ)
    (hr : ∀ μ, ¬ p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    ∃ C : ℝ, ∀ k, ‖u - (subspaceIterate A S k).starProjection u‖ ≤ C * (r / ‖l‖) ^ k := by
  obtain ⟨s, ⟨hs, hsu⟩, -⟩ := existsUnique_mem_spectralProjector_eq hdisj hrank hmem
  have hw : s - u ∈ ⨆ μ, ⨆ _ : ¬ p μ, A.maxGenEigenspace μ := by
    rw [← hsu]; exact sub_spectralProjector_mem s
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_iSup hw hr
  exact ⟨C, fun k => norm_sub_starProjection_subspaceIterate_le hl hu hs hC k⟩

/-- The iterated subspaces capture the dominant eigenvectors in the limit: under the dominance
`r < ‖λ‖` the orthogonal projections of `u` onto `A^k S` converge to `u`. -/
theorem tendsto_starProjection_subspaceIterate [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E]
    {p : 𝕜 → Prop} {u : E} {l : 𝕜} {r : ℝ}
    (hdisj : Disjoint S (⨆ μ, ⨆ _ : ¬ p μ, A.maxGenEigenspace μ))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 ↥(⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ))
    (hl : l ≠ 0) (hu : A u = l • u) (hmem : u ∈ ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ)
    (hr0 : 0 ≤ r) (hrl : r < ‖l‖) (hr : ∀ μ, ¬ p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    Tendsto (fun k => (subspaceIterate A S k).starProjection u) atTop (𝓝 u) := by
  obtain ⟨C, hC⟩ := exists_norm_sub_starProjection_subspaceIterate_le hdisj hrank hl hu hmem hr
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  have hbound : Tendsto (fun k : ℕ => C * (r / ‖l‖) ^ k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (r / ‖l‖) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr0 hl0.le) ((div_lt_one hl0).mpr hrl)
    simpa using h1.const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun k => ?_) hbound
  rw [norm_norm, norm_sub_rev]
  exact hC k

end SubspaceIteration

end Krylov

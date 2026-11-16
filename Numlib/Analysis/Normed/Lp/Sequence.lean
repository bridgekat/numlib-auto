/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.lpSpace` / `Mathlib.Analysis.Normed.Lp.lpHolder` (the
subspaces `c`, `c₀` and the duality) and `Mathlib.MeasureTheory.Function.LpSpace.Basic` (the
counting-measure bridge).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.MeasureTheory.Function.LpSpace.Clarkson

/-!
# The sequence spaces $\ell^p$, $c$ and $c_0$

Mathlib's `lp` is the space $\ell^p(\alpha, E)$ of families $x = (x_i)_{i \in \alpha}$ in a normed
space $E$ with $\sum_i \|x_i\|^p < \infty$, or with $\sup_i \|x_i\| < \infty$ when $p = \infty$.
Mathlib proves that it is a Banach space and gives Hölder's inequality and a duality pairing. This
module adds the facts about sequence spaces of [brezis2011functional], §11.3. It defines the space
$c$ of convergent sequences and the space $c_0$ of null sequences as closed subspaces of
$\ell^\infty(\mathbb{N}, E)$, and proves the inclusions $\ell^p \subseteq c_0$ for $p < \infty$ and
$\ell^p \subseteq \ell^q$ with $\|x\|_q \le \|x\|_p$ for $p \le q$. Over a field $\mathbb{K}$ (the
Lean `𝕜`) that is $\mathbb{R}$ or $\mathbb{C}$, it proves the dualities $(\ell^p)^* = \ell^{p'}$ for
$1 \le p < \infty$, $(c_0)^* = \ell^1$ and $c^* = \ell^1 \times \mathbb{K}$ (Propositions
11.18–11.20), the reflexivity and the uniform convexity of $\ell^p$ for $1 < p < \infty$
(Proposition 11.15), and the non-reflexivity of $c_0$, $\ell^\infty$, $c$ and $\ell^1$ (Proposition
11.21). It also proves that $\ell^p$ for $p < \infty$, $c_0$ and $c$ are separable when $E$ is
separable, and that $\ell^\infty$ over an infinite index set is not separable (Propositions 11.16
and 11.17).

The module also defines two standard operators: the right shift $S_r u = (0, u_0, u_1, \dots)$ on
$\ell^2(\mathbb{N}, \mathbb{K})$, and the diagonal operator $x \mapsto (\alpha_i x_i)_i$ on $\ell^p$
of a bounded family of scalars $\alpha$. Finally, it identifies $\ell^p(\alpha, E)$ with $L^p$ of
the counting measure on a countable set $\alpha$. Below, $p'$ is the conjugate exponent of $p$,
$e_k$ is the scalar sequence that is $1$ at index $k$ and $0$ elsewhere, and
$\varphi_u(x) = \sum_k u_k x_k$ is the functional of a sequence $u$.

## Main definitions

* `lp.convergent`: the space $c$ of sequences that have a limit, as a submodule of
  $\ell^\infty(\mathbb{N}, E)$.
* `lp.zeroAtInfty`: the space $c_0$ of sequences that tend to $0$, as a submodule of
  $\ell^\infty(\mathbb{N}, E)$.
* `lp.convergent.limCLM`: the limit $x \mapsto \lim_k x_k$, as a bounded linear map $c \to E$ of
  norm at most $1$.
* `lp.zeroAtInftyLIE`: the isometric isomorphism of $c_0$ with Mathlib's space $C_0(\mathbb{N}, E)$.
* `lp.inclusionCLM`: the inclusion $\ell^p \to \ell^q$ for $1 \le p \le q \le \infty$, a bounded
  linear map of norm at most $1$.
* `lp.shiftRightL`: the right shift on $\ell^2(\mathbb{N}, \mathbb{K})$.
* `lp.diagonalL`: the diagonal operator $x \mapsto (\alpha_i x_i)_i$ on $\ell^p$ of a bounded family
  of scalars.
* `lp.dualEquiv`: the isometric isomorphism $\ell^{p'} \cong (\ell^p)^*$, $u \mapsto \varphi_u$, for
  $1 \le p < \infty$.
* `lp.zeroAtInfty.dualEquiv`: the isometric isomorphism $\ell^1 \cong (c_0)^*$.
* `lp.convergent.dualEquiv`: the isometric isomorphism $\ell^1 \times \mathbb{K} \cong c^*$, $(u,
  \lambda) \mapsto (x \mapsto \sum_k u_k x_k + \lambda \lim x)$, for the norm $\|u\|_1 + |\lambda|$.
* `lp.lpLIELpCount`: the isometric isomorphism of $\ell^p(\alpha, E)$ with $L^p$ of the counting
  measure.

## Main results

* `lp.isClosed_zeroAtInfty`, `lp.isClosed_convergent`: $c_0$ is closed in $\ell^\infty$, and $c$ is
  closed when $E$ is complete.
* `lp.tendsto_cofinite_zero`: for $p < \infty$, the terms of a sequence in $\ell^p$ tend to $0$.
* `lp.norm_linearMapOfLE_le`: $\|x\|_q \le \|x\|_p$ for $0 < p \le q \le \infty$.
* `lp.norm_shiftRightL_apply`: the right shift is an isometry.
* `lp.diagonalL_single`: the unit vectors are eigenvectors of a diagonal operator.
* `lp.not_finiteDimensional_of_infinite`: $\ell^p$ over an infinite index set is
  infinite-dimensional.
* `lp.toDual_surjective`, `lp.zeroAtInfty.toDual_surjective`, `lp.convergent.toDual_surjective`:
  every bounded linear functional on $\ell^p$ ($p < \infty$), $c_0$ or $c$ comes from a sequence.
* `lp.isReflexive`: $\ell^p$ is reflexive for $1 < p < \infty$.
* `lp.zeroAtInfty.not_isReflexive`, `lp.not_isReflexive_top`, `lp.convergent.not_isReflexive`,
  `lp.not_isReflexive_one`: $c_0$, $\ell^\infty$, $c$ and $\ell^1$ are not reflexive.
* `lp.uniformConvexSpace`: $\ell^p(\alpha, \mathbb{R})$ is uniformly convex for $1 < p < \infty$ and
  countable $\alpha$.
* `lp.separableSpace`, `lp.zeroAtInfty.instSeparableSpace`, `lp.convergent.instSeparableSpace`:
  $\ell^p$ for $p < \infty$, $c_0$ and $c$ are separable when $E$ is separable.
* `lp.not_separableSpace_top`: $\ell^\infty$ over an infinite index set is not separable.

## Proof outline

The isometry property of each duality comes from the finite-section estimate of
[brezis2011functional]: for a functional $\varphi$ on $\ell^p$ and $u_k = \varphi(e_k)$, testing
$\varphi$ on the finitely supported sequence $x_k = |u_k|^{p'-2} \overline{u_k}$ gives
$\sum_{k \in s} |u_k|^{p'} \le \|\varphi\|^{p'}$ for every finite set $s$. The same estimate gives
the surjectivity: $u$ lies in $\ell^{p'}$, and $\varphi$ agrees with $\varphi_u$ on the unit
vectors, whose finite linear combinations are dense. Reflexivity of $\ell^p$ follows from the two
isometries $(\ell^p)^{**} \cong (\ell^{p'})^* \cong \ell^p$. The space $c_0$ is not reflexive
because the element $(1, 1, 1, \dots)$ of $(c_0)^{**} = (\ell^1)^* = \ell^\infty$ is not in $c_0$.
The spaces $\ell^\infty$ and $c$ contain $c_0$ as a closed subspace, and if $\ell^1$ were reflexive,
then its dual $\ell^\infty$ would be reflexive.

## Implementation notes

* The spaces $c$ and $c_0$ are submodules of `lp (fun _ : ℕ ↦ E) ∞`, not separate types, because the
  statements of [brezis2011functional] compare $c_0$, $c$ and $\ell^p$ inside $\ell^\infty$. The
  name `lp.zeroAtInfty` follows Mathlib's `ZeroAtInftyContinuousMap`.
* The dualities are stated for scalar sequences over `RCLike 𝕜`. The duality
  $(\ell^p)^* = \ell^{p'}$ holds for any index type. The product $\ell^1 \times \mathbb{K}$ is
  `WithLp 1 (lp (fun _ : ℕ ↦ 𝕜) 1 × 𝕜)`, whose norm is $\|u\|_1 + |\lambda|$.
* Reflexivity of $\ell^p$ is proved from the dualities directly. [brezis2011functional] applies
  Theorem 4.10 to the counting measure instead. Uniform convexity follows the route of the source,
  "Theorem 4.10 and Exercise 4.12 with $\Omega = \mathbb{N}$": it is transported from
  `MeasureTheory.Lp.instUniformConvexSpace` along `lp.lpLIELpCount`. This isometry also gives an
  $\ell^p$ version of every $L^p$ theorem.
* Uniform convexity is a property of real normed spaces, so it is stated for `lp (fun _ : α ↦ ℝ) p`.
-/

open Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace lp

/-! ### The subspaces $c$ and $c_0$ of $\ell^\infty$ -/

section Subspaces

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The space $c$ of [brezis2011functional], §11.3: the submodule of $\ell^\infty(\mathbb{N}, E)$ of
the sequences $x$ that converge to some $l \in E$.

A convergent sequence is bounded, so every convergent sequence lies in $\ell^\infty$. -/
def convergent : Submodule 𝕜 (lp (fun _ : ℕ => E) ∞) where
  carrier := {x | ∃ l : E, Tendsto (⇑x) atTop (𝓝 l)}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [lp.coeFn_add]; exact ha.add hb⟩
  zero_mem' := ⟨0, by rw [lp.coeFn_zero]; exact tendsto_const_nhds⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, by rw [lp.coeFn_smul]; exact ha.const_smul c⟩

/-- The space $c_0$ of [brezis2011functional], §11.3: the submodule of $\ell^\infty(\mathbb{N}, E)$
of the sequences $x$ with $x_k \to 0$.

The name follows Mathlib's `ZeroAtInftyContinuousMap`, the space $C_0(\mathbb{N}, E)$, to which
$c_0$ is isometric by `lp.zeroAtInftyLIE`. -/
def zeroAtInfty : Submodule 𝕜 (lp (fun _ : ℕ => E) ∞) where
  carrier := {x | Tendsto (⇑x) atTop (𝓝 0)}
  add_mem' := by
    intro x y hx hy
    rw [Set.mem_ofPred_eq, lp.coeFn_add]
    have h := hx.add hy
    rw [add_zero] at h
    exact h
  zero_mem' := by rw [Set.mem_ofPred_eq, lp.coeFn_zero]; exact tendsto_const_nhds
  smul_mem' := by
    intro c x hx
    rw [Set.mem_ofPred_eq, lp.coeFn_smul]
    have h := hx.const_smul c
    rw [smul_zero] at h
    exact h

variable {𝕜 E}

/-- An element $x$ of $\ell^\infty(\mathbb{N}, E)$ lies in $c$ if and only if $x_k \to l$ for some
$l \in E$. -/
@[simp]
theorem mem_convergent {x : lp (fun _ : ℕ => E) ∞} :
    x ∈ convergent 𝕜 E ↔ ∃ l : E, Tendsto (⇑x) atTop (𝓝 l) :=
  Iff.rfl

/-- An element $x$ of $\ell^\infty(\mathbb{N}, E)$ lies in $c_0$ if and only if $x_k \to 0$. -/
@[simp]
theorem mem_zeroAtInfty {x : lp (fun _ : ℕ => E) ∞} :
    x ∈ zeroAtInfty 𝕜 E ↔ Tendsto (⇑x) atTop (𝓝 0) :=
  Iff.rfl

variable (𝕜 E)

/-- Every null sequence converges: $c_0 \subseteq c$. -/
theorem zeroAtInfty_le_convergent : zeroAtInfty 𝕜 E ≤ convergent 𝕜 E := fun _ hx => ⟨0, hx⟩

/-- The space $c_0$ is closed in $\ell^\infty(\mathbb{N}, E)$: a uniform limit of null sequences is
a null sequence. This needs no completeness of $E$, because the limit $0$ is given. -/
theorem isClosed_zeroAtInfty : IsClosed (zeroAtInfty 𝕜 E : Set (lp (fun _ : ℕ => E) ∞)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  rw [SetLike.mem_coe, mem_zeroAtInfty, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (by positivity)
  rw [SetLike.mem_coe, mem_zeroAtInfty] at hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hy (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have h1 : ‖x n - y n‖ < ε / 2 := by
    refine (lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) n).trans_lt ?_
    rwa [← dist_eq_norm]
  have h2 : ‖y n‖ < ε / 2 := by simpa [dist_zero_right] using hN n hn
  calc ‖x n‖ = ‖(x n - y n) + y n‖ := by rw [sub_add_cancel]
    _ ≤ ‖x n - y n‖ + ‖y n‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

/-- If $E$ is complete, then $c$ is closed in $\ell^\infty(\mathbb{N}, E)$.

A uniform limit of convergent sequences is a Cauchy sequence, and it converges because $E$ is
complete. -/
theorem isClosed_convergent [CompleteSpace E] :
    IsClosed (convergent 𝕜 E : Set (lp (fun _ : ℕ => E) ∞)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  rw [SetLike.mem_coe, mem_convergent]
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 3) (by positivity)
  rw [SetLike.mem_coe, mem_convergent] at hy
  obtain ⟨l, hl⟩ := hy
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 3) (by positivity)
  have hxy' : ∀ k, dist (x k) (y k) < ε / 3 := fun k => by
    rw [dist_eq_norm]
    refine (lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) k).trans_lt ?_
    rwa [← dist_eq_norm]
  refine ⟨N, fun m hm n hn => ?_⟩
  calc dist (x m) (x n) ≤ dist (x m) (y m) + dist (y m) (y n) + dist (y n) (x n) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hxy' m
        · exact hN m hm n hn
        · rw [dist_comm]; exact hxy' n
    _ = ε := by ring

/-- If $E$ is a Banach space, then $c$ is a Banach space. -/
instance convergent.instCompleteSpace [CompleteSpace E] : CompleteSpace (convergent 𝕜 E) :=
  (isClosed_convergent 𝕜 E).completeSpace_coe

/-- If $E$ is a Banach space, then $c_0$ is a Banach space. -/
instance zeroAtInfty.instCompleteSpace [CompleteSpace E] : CompleteSpace (zeroAtInfty 𝕜 E) :=
  (isClosed_zeroAtInfty 𝕜 E).completeSpace_coe

/-- For $k \in \mathbb{N}$ and $a \in E$, the sequence $(0, \dots, 0, a, 0, \dots)$ with $a$ at
index $k$ lies in $c_0$. -/
theorem single_mem_zeroAtInfty (k : ℕ) (a : E) : lp.single ∞ k a ∈ zeroAtInfty 𝕜 E := by
  rw [mem_zeroAtInfty, lp.coeFn_single]
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k + 1, fun n hn => ?_⟩)
  exact (Pi.single_eq_of_ne (M := fun _ : ℕ => E) (show n ≠ k by omega) a).symm

end Subspaces

section Limit

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The map that sends $a \in E$ to the constant sequence $(a, a, a, \dots)$, as a bounded linear
map $E \to \ell^\infty(\mathbb{N}, E)$ of norm at most $1$. -/
def constL : E →L[𝕜] lp (fun _ : ℕ => E) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun _ => a, memℓp_infty ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun a => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg a) fun _ => le_rfl

/-- Every term of the constant sequence of $a$ is $a$. -/
@[simp]
theorem constL_apply (a : E) (n : ℕ) : constL 𝕜 E a n = a := rfl

/-- A constant sequence lies in $c$. -/
theorem constL_mem_convergent (a : E) : constL 𝕜 E a ∈ convergent 𝕜 E :=
  ⟨a, tendsto_const_nhds⟩

/-! ### The limit functional on $c$ -/

/-- The limit functional on $c$: the bounded linear map $c \to E$,
$x \mapsto \lim_{k \to \infty} x_k$, of norm at most $1$. It gives the term $\lambda \lim x_k$
in Proposition 11.20 of [brezis2011functional]. -/
def convergent.limCLM : convergent 𝕜 E →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun x => limUnder atTop (⇑(x : lp (fun _ : ℕ => E) ∞))
      map_add' := fun x y => by
        obtain ⟨a, ha⟩ := x.2
        obtain ⟨b, hb⟩ := y.2
        have hab : Tendsto (⇑((x + y : convergent 𝕜 E) : lp (fun _ : ℕ => E) ∞)) atTop
            (𝓝 (a + b)) := by
          rw [Submodule.coe_add, lp.coeFn_add]
          exact ha.add hb
        rw [ha.limUnder_eq, hb.limUnder_eq, hab.limUnder_eq]
      map_smul' := fun c x => by
        obtain ⟨a, ha⟩ := x.2
        have hca : Tendsto (⇑((c • x : convergent 𝕜 E) : lp (fun _ : ℕ => E) ∞)) atTop
            (𝓝 (c • a)) := by
          rw [Submodule.coe_smul, lp.coeFn_smul]
          exact ha.const_smul c
        rw [RingHom.id_apply, ha.limUnder_eq, hca.limUnder_eq] }
    1 fun x => by
      obtain ⟨a, ha⟩ := x.2
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, ha.limUnder_eq]
      exact le_of_tendsto' ha.norm fun n => lp.norm_apply_le_norm ENNReal.top_ne_zero _ n

variable {𝕜 E}

/-- For $x \in c$, the sequence $x$ converges to the value of the limit functional
`lp.convergent.limCLM` at $x$. -/
theorem convergent.tendsto_limCLM (x : convergent 𝕜 E) :
    Tendsto (⇑(x : lp (fun _ : ℕ => E) ∞)) atTop (𝓝 (convergent.limCLM 𝕜 E x)) := by
  obtain ⟨a, ha⟩ := x.2
  have : convergent.limCLM 𝕜 E x = a := ha.limUnder_eq
  rw [this]
  exact ha

/-- If $x \in c$ converges to $a$, then the limit functional takes the value $a$ at $x$. -/
theorem convergent.limCLM_eq_of_tendsto {x : convergent 𝕜 E} {a : E}
    (hx : Tendsto (⇑(x : lp (fun _ : ℕ => E) ∞)) atTop (𝓝 a)) : convergent.limCLM 𝕜 E x = a :=
  tendsto_nhds_unique (convergent.tendsto_limCLM x) hx

/-- For $x \in c$, the limit satisfies $\|\lim x\| \le \|x\|_\infty$. -/
theorem convergent.norm_limCLM_apply_le (x : convergent 𝕜 E) :
    ‖convergent.limCLM 𝕜 E x‖ ≤ ‖x‖ :=
  le_of_tendsto' (convergent.tendsto_limCLM x).norm fun n =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ n

variable (𝕜 E) in
/-- The limit functional on $c$ has operator norm at most $1$. -/
theorem convergent.norm_limCLM_le : ‖convergent.limCLM 𝕜 E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The limit functional vanishes on $c_0$: if $x \in c$ is a null sequence, then $\lim x = 0$. -/
theorem convergent.limCLM_eq_zero_of_mem_zeroAtInfty {x : convergent 𝕜 E}
    (hx : (x : lp (fun _ : ℕ => E) ∞) ∈ zeroAtInfty 𝕜 E) : convergent.limCLM 𝕜 E x = 0 :=
  convergent.limCLM_eq_of_tendsto hx

/-- The limit of the constant sequence of $a$ is $a$. -/
@[simp]
theorem convergent.limCLM_constL (a : E) :
    convergent.limCLM 𝕜 E ⟨constL 𝕜 E a, constL_mem_convergent 𝕜 E a⟩ = a :=
  convergent.limCLM_eq_of_tendsto tendsto_const_nhds

/-- For $x \in c$, the sequence $x - (\lim x) (1, 1, 1, \dots)$ lies in $c_0$. This gives the
decomposition of $c$ into $c_0$ and the constant sequences, which the proof of Proposition 11.20
of [brezis2011functional] uses. -/
theorem convergent.sub_constL_limCLM_mem_zeroAtInfty (x : convergent 𝕜 E) :
    (x : lp (fun _ : ℕ => E) ∞) - constL 𝕜 E (convergent.limCLM 𝕜 E x) ∈ zeroAtInfty 𝕜 E := by
  rw [mem_zeroAtInfty, lp.coeFn_sub]
  have h := (convergent.tendsto_limCLM x).sub_const (convergent.limCLM 𝕜 E x)
  rw [sub_self] at h
  exact h

end Limit

/-! ### The inclusions $\ell^p \subseteq c_0$ and $\ell^p \subseteq \ell^q$ -/

section Inclusions

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p q : ℝ≥0∞}

/-- Let $p < \infty$ and let $f \in \ell^p(\alpha, E)$, where the space $E_i$ may depend on the
index $i$. Then $\|f_i\| \to 0$ along the cofinite filter on $\alpha$.

For $0 < p < \infty$, this follows from the summability of $\|f_i\|^p$. -/
theorem tendsto_norm_cofinite_zero (hp : p ≠ ∞) (f : lp E p) :
    Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have hfin := (lp.memℓp f).finite_dsupport
    refine tendsto_const_nhds.congr' (hfin.eventually_cofinite_notMem.mono fun i hi => ?_)
    simp only [Set.mem_ofPred_eq, not_not] at hi
    simp [hi]
  · have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have h := ((lp.memℓp f).summable hP).tendsto_cofinite_zero
    have hc :=
      ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 1 / p.toReal)).tendsto 0).comp h
    rw [Real.zero_rpow (by positivity)] at hc
    refine hc.congr fun i => ?_
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hP.ne', Real.rpow_one]

/-- Let $p < \infty$ and let $f \in \ell^p(\alpha, E)$. Then $f_i \to 0$ along the cofinite filter
on $\alpha$. This is the inclusion $\ell^p \subseteq c_0$ of [brezis2011functional], §11.3.

For $\alpha = \mathbb{N}$, the cofinite filter is the filter `atTop`, so the statement is
$f_k \to 0$ as $k \to \infty$. -/
theorem tendsto_cofinite_zero {E : Type*} [NormedAddCommGroup E] (hp : p ≠ ∞)
    (f : lp (fun _ : α => E) p) : Tendsto (fun i => f i) cofinite (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_cofinite_zero hp f)

/-- Let $p < \infty$. For $f \in \ell^p(\mathbb{N}, E)$, the image of $f$ under Mathlib's inclusion
`lp.linearMapOfLE` into $\ell^\infty(\mathbb{N}, E)$ lies in $c_0$. This is the inclusion
$\ell^p \subseteq c_0$ of [brezis2011functional], §11.3, as an inclusion of subspaces of
$\ell^\infty$. -/
theorem linearMapOfLE_mem_zeroAtInfty (𝕜 : Type*) [NormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (hp : p ≠ ∞) (f : lp (fun _ : ℕ => E) p) :
    lp.linearMapOfLE 𝕜 (fun _ : ℕ => E) le_top f ∈ zeroAtInfty 𝕜 E := by
  rw [mem_zeroAtInfty, lp.coe_linearMapOfLE_apply, ← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero hp f

/-- Let $0 < p \le q \le \infty$ and let $f \in \ell^p(\alpha, E)$. Then $\|f\|_q \le \|f\|_p$,
where $f$ is regarded as an element of $\ell^q$ by Mathlib's inclusion `lp.linearMapOfLE`. This
is the inclusion $\ell^p \subseteq \ell^q$ with $\|x\|_q \le \|x\|_p$ of [brezis2011functional],
§11.3.

The proof bounds $\|f_i\|^q = \|f_i\|^p \|f_i\|^{q-p} \le \|f_i\|^p \|f\|_p^{q-p}$ and sums over
$i$. -/
theorem norm_linearMapOfLE_le (𝕜 : Type*) [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)]
    [∀ i, IsBoundedSMul 𝕜 (E i)] (hp : p ≠ 0) (h : p ≤ q) (f : lp E p) :
    ‖lp.linearMapOfLE 𝕜 E h f‖ ≤ ‖f‖ := by
  have hfi : ∀ i, ‖f i‖ ≤ ‖f‖ := lp.norm_apply_le_norm hp f
  rcases eq_or_ne q ∞ with rfl | hq
  · exact lp.norm_le_of_forall_le (lp.norm_nonneg' f) fun i => by
      rw [lp.coe_linearMapOfLE_apply]; exact hfi i
  · have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq h
    have hP : 0 < p.toReal := ENNReal.toReal_pos hp hp'
    have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq h
    have hQ : 0 < q.toReal := hP.trans_le hPQ
    have hQP : p.toReal + (q.toReal - p.toReal) ≠ 0 := by rw [add_sub_cancel]; exact hQ.ne'
    refine lp.norm_le_of_forall_sum_le hQ (lp.norm_nonneg' f) fun s => ?_
    simp only [lp.coe_linearMapOfLE_apply]
    calc ∑ i ∈ s, ‖f i‖ ^ q.toReal
        = ∑ i ∈ s, ‖f i‖ ^ p.toReal * ‖f i‖ ^ (q.toReal - p.toReal) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.rpow_add' (norm_nonneg _) hQP, add_sub_cancel]
      _ ≤ ∑ i ∈ s, ‖f i‖ ^ p.toReal * ‖f‖ ^ (q.toReal - p.toReal) := by
          gcongr with i hi
          exact hfi i
      _ = (∑ i ∈ s, ‖f i‖ ^ p.toReal) * ‖f‖ ^ (q.toReal - p.toReal) := by rw [Finset.sum_mul]
      _ ≤ ‖f‖ ^ p.toReal * ‖f‖ ^ (q.toReal - p.toReal) :=
          mul_le_mul_of_nonneg_right (lp.sum_rpow_le_norm_rpow hP f s)
            (Real.rpow_nonneg (lp.norm_nonneg' f) _)
      _ = ‖f‖ ^ q.toReal := by rw [← Real.rpow_add' (lp.norm_nonneg' f) hQP, add_sub_cancel]

end Inclusions

section InclusionCLM

variable {α : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : α → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {p q : ℝ≥0∞}

/-- For $1 \le p \le q \le \infty$, the inclusion $\ell^p(\alpha, E) \to \ell^q(\alpha, E)$, as a
bounded linear map of norm at most $1$ (`lp.norm_inclusionCLM_le`). -/
def inclusionCLM [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p ≤ q) : lp E p →L[𝕜] lp E q :=
  (lp.linearMapOfLE 𝕜 E h).mkContinuous 1 fun f => by
    rw [one_mul]
    exact norm_linearMapOfLE_le 𝕜 (zero_lt_one.trans_le Fact.out).ne' h f

variable {E}

/-- The inclusion $\ell^p \to \ell^q$ does not change the underlying family. -/
@[simp]
theorem coe_inclusionCLM_apply [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p ≤ q) (f : lp E p) :
    ⇑(inclusionCLM 𝕜 E h f) = f :=
  lp.coe_linearMapOfLE_apply h f

/-- For $1 \le p \le q \le \infty$, the inclusion $\ell^p \to \ell^q$ has operator norm at most $1$.
-/
theorem norm_inclusionCLM_le [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p ≤ q) :
    ‖inclusionCLM 𝕜 E h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end InclusionCLM

/-! ### The right shift on $\ell^2$ -/

section Shift

variable (𝕜 : Type*) [NormedField 𝕜]

/-- The right-shifted sequence $(0, u_0, u_1, \dots)$ of a sequence $u$. -/
private def shiftFun (u : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => u n

private theorem shiftFun_zero (u : ℕ → 𝕜) : shiftFun 𝕜 u 0 = 0 := rfl

private theorem shiftFun_succ (u : ℕ → 𝕜) (n : ℕ) : shiftFun 𝕜 u (n + 1) = u n := rfl

private theorem memℓp_shiftFun (u : lp (fun _ : ℕ => 𝕜) 2) : Memℓp (shiftFun 𝕜 u) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  exact (summable_nat_add_iff 1).1 ((memℓp_gen_iff (by norm_num)).1 u.2)

private theorem norm_shiftFun (u : lp (fun _ : ℕ => 𝕜) 2) :
    ‖(⟨shiftFun 𝕜 u, memℓp_shiftFun 𝕜 u⟩ : lp (fun _ : ℕ => 𝕜) 2)‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  have hs := (memℓp_gen_iff (by norm_num)).1 (memℓp_shiftFun 𝕜 u)
  change ∑' i, ‖shiftFun 𝕜 u i‖ ^ (2 : ℝ≥0∞).toReal = _
  rw [hs.tsum_eq_zero_add]
  simp [shiftFun_zero, shiftFun_succ]

/-- The **right shift** on $\ell^2(\mathbb{N}, \mathbb{K})$, for a normed field $\mathbb{K}$: the
bounded linear operator $S_r u = (0, u_0, u_1, \dots)$, that is, $(S_r u)_0 = 0$ and
$(S_r u)_{n+1} = u_n$.

The right shift is an isometry (`lp.norm_shiftRightL_apply`), so it is injective, and it is not
surjective. It is the standard example of an operator for which $0$ is in the spectrum but is
not an eigenvalue ([brezis2011functional], chapter 6, Remark 6). Over $\mathbb{C}$ it is an
example of an operator without eigenvalues ([brezis2011functional], §11.4). -/
def shiftRightL : lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨shiftFun 𝕜 u, memℓp_shiftFun 𝕜 u⟩
      map_add' := fun u v => lp.ext (funext fun n => by
        cases n with
        | zero => change (0 : 𝕜) = 0 + 0; rw [add_zero]
        | succ n => rfl)
      map_smul' := fun c u => lp.ext (funext fun n => by
        cases n with
        | zero => change (0 : 𝕜) = c • 0; rw [smul_zero]
        | succ n => rfl) }
    1 fun u => by
      rw [one_mul]
      exact (norm_shiftFun 𝕜 u).le

/-- The first term of a right-shifted sequence is $(S_r u)_0 = 0$. -/
@[simp]
theorem shiftRightL_apply_zero (u : lp (fun _ : ℕ => 𝕜) 2) : shiftRightL 𝕜 u 0 = 0 := rfl

/-- The right shift satisfies $(S_r u)_{n+1} = u_n$ for every $n$. -/
@[simp]
theorem shiftRightL_apply_succ (u : lp (fun _ : ℕ => 𝕜) 2) (n : ℕ) :
    shiftRightL 𝕜 u (n + 1) = u n := rfl

/-- The right shift is an isometry: $\|S_r u\| = \|u\|$ for every $u \in \ell^2$. -/
theorem norm_shiftRightL_apply (u : lp (fun _ : ℕ => 𝕜) 2) : ‖shiftRightL 𝕜 u‖ = ‖u‖ :=
  norm_shiftFun 𝕜 u

end Shift

/-! ### Diagonal operators on $\ell^p$ -/

section Diagonal

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Let $\alpha = (\alpha_i)_{i \in \iota}$ be a family of scalars with $\|\alpha_i\| \le C$ for all
$i$, and let $x \in \ell^p$, for any exponent $0 \le p \le \infty$. Then the family
$(\alpha_i x_i)_i$ lies in $\ell^p$. -/
theorem memℓp_smul_of_forall_norm_le {α : ι → 𝕜} {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) (x : lp E p) :
    Memℓp (fun i ↦ α i • x i) p :=
  ((lp.memℓp x).norm.const_mul C).mono fun i ↦
    (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hα i) (norm_nonneg _))

private theorem norm_smul_le_abs_mul_norm {α : ι → 𝕜} {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C)
    (x : lp E p) :
    ‖(⟨fun i ↦ α i • x i, memℓp_smul_of_forall_norm_le hα x⟩ : lp E p)‖ ≤ |C| * ‖x‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  let y : lp (fun _ : ι ↦ ℝ) p := ⟨fun i ↦ ‖x i‖, (lp.memℓp x).norm⟩
  calc ‖(⟨fun i ↦ α i • x i, memℓp_smul_of_forall_norm_le hα x⟩ : lp E p)‖
      ≤ ‖C • y‖ := lp.norm_mono hp fun i ↦ by
        change ‖α i • x i‖ ≤ ‖(C • y) i‖
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_norm]
        exact (norm_smul_le _ _).trans
          (mul_le_mul_of_nonneg_right ((hα i).trans (le_abs_self C)) (norm_nonneg _))
    _ ≤ ‖C‖ * ‖y‖ := lp.norm_const_smul_le hp C y
    _ ≤ |C| * ‖x‖ := by
        rw [Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left (lp.norm_mono hp fun i ↦ ?_) (abs_nonneg C)
        change ‖‖x i‖‖ ≤ ‖x i‖
        exact (norm_norm _).le

variable (E p) in
/-- The **diagonal operator** of a bounded family of scalars. Let $1 \le p \le \infty$ and let
$\alpha = (\alpha_i)_{i \in \iota}$ be scalars with $\|\alpha_i\| \le C$ for all $i$. The
diagonal operator is the bounded linear operator $T$ on $\ell^p$ with $(Tx)_i = \alpha_i x_i$.
It has norm at most $|C|$ (`lp.norm_diagonalL_le`), and the unit vectors are eigenvectors:
$T(\delta_i a) = \alpha_i \, \delta_i a$, where $\delta_i a$ is the family that is $a$ at index
$i$ and $0$ elsewhere (`lp.diagonalL_single`).

On $\ell^2$ this is the multiplication operator of [brezis2011functional], chapter 6, Remark 7,
and of Exercises 6.1 and 6.17 there. -/
def diagonalL (α : ι → 𝕜) {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) : lp E p →L[𝕜] lp E p :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨fun i ↦ α i • x i, memℓp_smul_of_forall_norm_le hα x⟩
      map_add' := fun x y ↦ lp.ext (funext fun i ↦ by
        change α i • (x + y) i = α i • x i + α i • y i
        rw [lp.coeFn_add, Pi.add_apply, smul_add])
      map_smul' := fun c x ↦ lp.ext (funext fun i ↦ by
        change α i • (c • x) i = c • (α i • x i)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_comm]) }
    |C| fun x ↦ norm_smul_le_abs_mul_norm hα x

/-- The diagonal operator acts by $(Tx)_i = \alpha_i x_i$. -/
@[simp]
theorem diagonalL_apply (α : ι → 𝕜) {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) (x : lp E p) (i : ι) :
    diagonalL E p α hα x i = α i • x i :=
  rfl

/-- The diagonal operator satisfies $\|Tx\| \le |C| \, \|x\|$ for every $x \in \ell^p$. -/
theorem norm_diagonalL_apply_le (α : ι → 𝕜) {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) (x : lp E p) :
    ‖diagonalL E p α hα x‖ ≤ |C| * ‖x‖ :=
  norm_smul_le_abs_mul_norm hα x

/-- The diagonal operator has operator norm at most $|C|$. -/
theorem norm_diagonalL_le (α : ι → 𝕜) {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) :
    ‖diagonalL E p α hα‖ ≤ |C| :=
  LinearMap.mkContinuous_norm_le _ (abs_nonneg C) _

/-- Let $\alpha$ and $\beta$ be bounded families of scalars, and let $\|\alpha_i - \beta_i\| \le G$
for all $i$. Then the difference of the diagonal operators of $\alpha$ and $\beta$ is the
diagonal operator of $\alpha - \beta$. -/
theorem diagonalL_sub (α β : ι → 𝕜) {C D : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) (hβ : ∀ i, ‖β i‖ ≤ D)
    {G : ℝ} (hαβ : ∀ i, ‖α i - β i‖ ≤ G) :
    diagonalL E p α hα - diagonalL E p β hβ = diagonalL E p (α - β) hαβ := by
  ext x i
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagonalL_apply, diagonalL_apply, diagonalL_apply,
    Pi.sub_apply, sub_smul]

/-- The unit vectors are eigenvectors of the diagonal operator: if $\delta_i a$ is the family that
is $a \in E_i$ at index $i$ and $0$ elsewhere, then $T(\delta_i a) = \alpha_i \, \delta_i a$. -/
theorem diagonalL_single [DecidableEq ι] (α : ι → 𝕜) {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) (i : ι)
    (a : E i) : diagonalL E p α hα (lp.single p i a) = α i • lp.single p i a := by
  ext j
  rw [diagonalL_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  by_cases h : j = i
  · subst h
    rfl
  · rw [Pi.single_eq_of_ne h, smul_zero, smul_zero]

/-- Let the spaces $E_i$ be finite-dimensional, and let $\alpha_i = 0$ for every $i$ outside a
finite set $s$. Then the diagonal operator of $\alpha$ has finite rank: its range is
finite-dimensional.

The range lies in the subspace of the families that vanish outside $s$. -/
theorem finiteDimensional_range_diagonalL [∀ i, FiniteDimensional 𝕜 (E i)]
    (α : ι → 𝕜) {C : ℝ} (hα : ∀ i, ‖α i‖ ≤ C) (s : Finset ι) (hs : ∀ i ∉ s, α i = 0) :
    FiniteDimensional 𝕜 (LinearMap.range (diagonalL E p α hα : lp E p →ₗ[𝕜] lp E p)) := by
  classical
  refine Submodule.finiteDimensional_of_le
    (S₂ := s.sup fun i ↦ LinearMap.range (lp.lsingle (𝕜 := 𝕜) (E := E) p i)) fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hy
  have hx : diagonalL E p α hα x = ∑ i ∈ s, lp.single p i (α i • x i) := by
    ext j
    rw [lp.coeFn_sum, Finset.sum_apply, diagonalL_apply]
    by_cases hj : j ∈ s
    · rw [Finset.sum_eq_single_of_mem j hj fun i _ hij ↦ lp.single_apply_ne p i _ hij.symm,
        lp.single_apply_self]
    · rw [hs j hj, zero_smul]
      exact (Finset.sum_eq_zero fun i hi ↦
        lp.single_apply_ne p i (α i • x i) (j := j) fun hji ↦ hj (by rw [hji]; exact hi)).symm
  rw [ContinuousLinearMap.coe_coe, hx]
  exact Submodule.sum_mem _ fun i hi ↦
    (Finset.le_sup (f := fun i ↦ LinearMap.range (lp.lsingle (𝕜 := 𝕜) (E := E) p i)) hi)
      (LinearMap.mem_range_self _ _)

omit [Fact (1 ≤ p)] in
/-- Let $\mathbb{K}$ be a nontrivially normed field. If the index set $\iota$ is infinite, then
$\ell^p(\iota, \mathbb{K})$ is infinite-dimensional over $\mathbb{K}$, for every exponent
$0 \le p \le \infty$. The proof uses that the unit vectors are linearly independent. -/
theorem not_finiteDimensional_of_infinite [Infinite ι] :
    ¬ FiniteDimensional 𝕜 (lp (fun _ : ι ↦ 𝕜) p) := by
  classical
  intro h
  have hli : LinearIndependent 𝕜 fun i : ι ↦ lp.single p i (1 : 𝕜) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have := congrArg (fun z : lp (fun _ : ι ↦ 𝕜) p ↦ z i) hg
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hi,
      ite_true, lp.coeFn_zero, Pi.zero_apply] at this
    exact this
  exact Module.Finite.not_linearIndependent_of_infinite _ hli

end Diagonal

/-! ### Finitely supported sequences in $c_0$, and the isometry with $C_0(\mathbb{N}, E)$ -/

section ZeroAtInfty

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every null sequence is the sum of its terms in $\ell^\infty$: if $x \in c_0$, then the series
$\sum_k \delta_k x_k$ converges unconditionally to $x$ in $\ell^\infty(\mathbb{N}, E)$, where
$\delta_k x_k$ is the sequence that is $x_k$ at index $k$ and $0$ elsewhere.

This is the analogue of Mathlib's `lp.hasSum_single` for $p = \infty$. For $p = \infty$ it holds
exactly on $c_0$. -/
theorem zeroAtInfty.hasSum_single {x : lp (fun _ : ℕ => E) ∞} (hx : x ∈ zeroAtInfty 𝕜 E) :
    HasSum (fun k => lp.single ∞ k (x k)) x := by
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx (ε / 2) (by positivity)
  refine eventually_atTop.2 ⟨Finset.range N, fun s hs => ?_⟩
  rw [dist_eq_norm]
  refine (lp.norm_le_of_forall_le (C := ε / 2) (half_pos hε).le fun j => ?_).trans_lt
    (half_lt_self hε)
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hj
  · rw [sub_self, _root_.norm_zero]
    positivity
  · have hNj : N ≤ j := by
      by_contra h
      exact hj (hs (Finset.mem_range.2 (not_le.1 h)))
    rw [zero_sub, _root_.norm_neg]
    simpa [dist_zero_right] using (hN j hNj).le

/-- Every $x \in c_0$ is the unconditional sum in $c_0$ of the sequences $\delta_k x_k$, where
$\delta_k x_k$ is $x_k$ at index $k$ and $0$ elsewhere. This is `lp.zeroAtInfty.hasSum_single`
with the sum taken in the subspace $c_0$. -/
theorem zeroAtInfty.hasSum_single' (x : zeroAtInfty 𝕜 E) :
    HasSum (fun k => (⟨lp.single ∞ k ((x : lp (fun _ : ℕ => E) ∞) k),
      single_mem_zeroAtInfty 𝕜 E k _⟩ : zeroAtInfty 𝕜 E)) x := by
  have hind : Topology.IsInducing (zeroAtInfty 𝕜 E).subtype := Topology.IsInducing.subtypeVal
  exact (hind.hasSum_iff _ _).1 (zeroAtInfty.hasSum_single x.2)

variable (𝕜 E)

open scoped ZeroAtInfty in
/-- The space $c_0$ is isometrically isomorphic to Mathlib's space $C_0(\mathbb{N}, E)$ of
continuous functions on $\mathbb{N}$ that vanish at infinity (`ZeroAtInftyContinuousMap`). The
isomorphism is the identity on the underlying functions.

On the discrete space $\mathbb{N}$ every function is continuous, the cocompact filter is the
filter `atTop`, and both norms are the supremum norm. -/
def zeroAtInftyLIE : zeroAtInfty 𝕜 E ≃ₗᵢ[𝕜] C₀(ℕ, E) where
  toFun x :=
    { toFun := ⇑(x : lp (fun _ : ℕ => E) ∞)
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]; exact x.2 }
  invFun f :=
    ⟨⟨⇑f, memℓp_infty (by
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.isBounded_range
      exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC _ (Set.mem_range_self i)⟩)⟩, by
      rw [mem_zeroAtInfty, ← Nat.cofinite_eq_atTop, ← cocompact_eq_cofinite]
      exact zero_at_infty f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖(_ : C₀(ℕ, E)).toBCF‖ = ‖(x : lp (fun _ : ℕ => E) ∞)‖
    rw [BoundedContinuousFunction.norm_eq_iSup_norm, lp.norm_eq_ciSup]
    rfl

/-- The isometric isomorphism of $c_0$ with $C_0(\mathbb{N}, E)$ does not change the terms of a
sequence. -/
@[simp]
theorem zeroAtInftyLIE_apply (x : zeroAtInfty 𝕜 E) (n : ℕ) :
    zeroAtInftyLIE 𝕜 E x n = (x : lp (fun _ : ℕ => E) ∞) n :=
  rfl

end ZeroAtInfty

/-! ### The duality $(\ell^p)^* = \ell^{p'}$ -/

section Duality

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} {p q : ℝ≥0∞}

/-- The **finite-section estimate**. Let $p$ and $q$ be conjugate exponents with
$1 \le p \le \infty$ and $1 \le q < \infty$, let $\varphi$ be a bounded linear functional on
$\ell^p(\alpha, \mathbb{K})$, and let $u_k = \varphi(e_k)$. Then for every finite set $s$ of
indices,
$$\sum_{k \in s} |u_k|^q \le \|\varphi\|^q.$$
This is display (6) in the proof of Proposition 11.18 of [brezis2011functional], before the
limit $N \to \infty$.

The proof tests $\varphi$ on the sequence with $x_k = |u_k|^{q-2} \overline{u_k}$ for $k \in s$
and $x_k = 0$ otherwise, so that $u_k x_k = |u_k|^q$. The estimate gives both the isometry
property and the surjectivity of `lp.toDual`. -/
theorem sum_norm_rpow_apply_single_le [DecidableEq α] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hq : q ≠ ∞) (φ : StrongDual 𝕜 (lp (fun _ : α => 𝕜) p))
    (s : Finset α) :
    ∑ k ∈ s, ‖φ (lp.single p k 1)‖ ^ q.toReal ≤ ‖φ‖ ^ q.toReal := by
  set Q := q.toReal with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hq Fact.out
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  obtain ⟨v, hv⟩ : ∃ v : α → 𝕜, ∀ k, v k = φ (lp.single p k 1) := ⟨_, fun _ => rfl⟩
  simp only [← hv]
  set c : α → 𝕜 := fun k => ((‖v k‖ ^ (Q - 2) : ℝ) : 𝕜) * (starRingEnd 𝕜) (v k) with hc
  set x : lp (fun _ : α => 𝕜) p := ∑ k ∈ s, lp.single p k (c k) with hx
  set S := ∑ k ∈ s, ‖v k‖ ^ Q with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (norm_nonneg _) _
  -- `φ x = S`
  have hcv : ∀ k, c k * v k = ((‖v k‖ ^ Q : ℝ) : 𝕜) := fun k => by
    rw [hc, mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
      ← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg _) (by norm_num; exact hQ0.ne')]
    norm_num
  have hφx : φ x = (S : 𝕜) := by
    rw [hx, map_sum, hS, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : (lp.single p k (c k) : lp (fun _ : α => 𝕜) p) = c k • lp.single p k 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul, ← hv, hcv]
  have hφx' : S ≤ ‖φ‖ * ‖x‖ := by
    have : ‖φ x‖ = S := by rw [hφx, RCLike.norm_ofReal, abs_of_nonneg hS0]
    rw [← this]
    exact φ.le_opNorm x
  rcases eq_or_ne p ∞ with hp | hp
  · -- `p = ∞`, `q = 1`: the test vector has norm at most `1`
    have hq1 : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).1 hp
    have hQ1' : Q = 1 := by rw [hQ, hq1, ENNReal.toReal_one]
    subst hp
    have hx1 : ‖x‖ ≤ 1 := by
      refine lp.norm_le_of_forall_le zero_le_one fun j => ?_
      rw [hx, lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_single, Finset.sum_pi_single]
      split_ifs with hj
      · rw [hc, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hQ1']
        rcases eq_or_ne (v j) 0 with h0 | h0
        · rw [h0, _root_.norm_zero, mul_zero]; exact zero_le_one
        · rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
            inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [_root_.norm_zero]; exact zero_le_one
    rw [hQ1', Real.rpow_one]
    simp only [hQ1', Real.rpow_one] at hS
    rw [hS] at hφx' ⊢
    calc ∑ k ∈ s, ‖v k‖ ≤ ‖φ‖ * ‖x‖ := hφx'
      _ ≤ ‖φ‖ * 1 := by gcongr
      _ = ‖φ‖ := mul_one _
  · -- `1 < p < ∞`: `‖x‖ ^ p = S`
    have hPQ : p.toReal.HolderConjugate Q := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    set P := p.toReal with hP
    have hP0 : 0 < P := hPQ.pos
    have hQ1'' : 1 < Q := hPQ.symm.lt
    have hxnorm : ‖x‖ ^ P = S := by
      rw [hx, lp.norm_sum_single hP0, hS]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck : ‖c k‖ = ‖v k‖ ^ (Q - 1) := by
        rw [hc, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), show Q - 1 = Q - 2 + 1 by ring,
          Real.rpow_add_one' (norm_nonneg _) (by intro h; linarith)]
      rw [hck, ← Real.rpow_mul (norm_nonneg _), hPQ.symm.sub_one_mul_conj]
    have hSle : S ≤ ‖φ‖ * S ^ (1 / P) := by
      have h2 : ‖x‖ = S ^ (1 / P) := by
        rw [← hxnorm, one_div, Real.rpow_rpow_inv (lp.norm_nonneg' x) hP0.ne']
      rwa [h2] at hφx'
    rcases hS0.eq_or_lt with hS0' | hSpos
    · rw [← hS0']
      exact Real.rpow_nonneg (norm_nonneg φ) _
    · have h3 : S ^ (1 / Q) ≤ ‖φ‖ := by
        have hsub : 1 / Q = 1 - 1 / P := by rw [one_div, one_div, hPQ.one_sub_inv]
        rw [hsub, Real.rpow_sub hSpos, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hSpos _)]
        exact hSle
      calc S = (S ^ (1 / Q)) ^ Q := by
            rw [← Real.rpow_mul hS0, one_div_mul_cancel hQ0.ne', Real.rpow_one]
        _ ≤ ‖φ‖ ^ Q := Real.rpow_le_rpow (Real.rpow_nonneg hS0 _) h3 hQ0.le

variable (𝕜 α p q) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Let $p$ and $q$ be conjugate exponents with $1 \le p, q \le \infty$. The map that sends
$u \in \ell^q(\alpha, \mathbb{K})$ to the functional $\varphi_u(x) = \sum_k u_k x_k$ on
$\ell^p(\alpha, \mathbb{K})$, as a bounded linear map $\ell^q \to (\ell^p)^*$.

It is Mathlib's `lp.dualPairing` for the multiplication of $\mathbb{K}$. Its isometry property
is `lp.norm_toDualCLM_apply`, and `lp.toDual` is the bundled linear isometry. -/
def toDualCLM : lp (fun _ : α => 𝕜) q →L[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p) :=
  lp.dualPairing q p (fun _ => ContinuousLinearMap.mul 𝕜 𝕜) (K := 1) fun _ =>
    (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜).trans_eq NNReal.coe_one.symm

variable {𝕜 α p q}

/-- The functional of $u$ is $\varphi_u(x) = \sum_k u_k x_k$. -/
theorem toDualCLM_apply (u : lp (fun _ : α => 𝕜) q) (x : lp (fun _ : α => 𝕜) p) :
    toDualCLM 𝕜 α p q u x = ∑' k, u k * x k :=
  rfl

variable (𝕜 α p q) in
/-- By Hölder's inequality, the map $u \mapsto \varphi_u$ from $\ell^q$ to $(\ell^p)^*$ has operator
norm at most $1$. -/
theorem norm_toDualCLM_le : ‖toDualCLM 𝕜 α p q‖ ≤ 1 :=
  (lp.norm_dualPairing (p := q) (q := p) (fun _ : α => ContinuousLinearMap.mul 𝕜 𝕜) (K := 1)
    fun _ => (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜).trans_eq NNReal.coe_one.symm).trans_eq
    NNReal.coe_one

/-- The functional of $u$ on a multiple of a unit vector is $\varphi_u(a e_k) = u_k a$. -/
theorem toDualCLM_single [DecidableEq α] (u : lp (fun _ : α => 𝕜) q) (k : α) (a : 𝕜) :
    toDualCLM 𝕜 α p q u (lp.single p k a) = u k * a := by
  rw [toDualCLM_apply, tsum_eq_single k fun j hj => by
    rw [lp.single_apply, Pi.single_eq_of_ne hj, mul_zero]]
  rw [lp.single_apply, Pi.single_eq_same]

/-- Let $p$ and $q$ be conjugate exponents with $1 \le p, q \le \infty$. For every
$u \in \ell^q(\alpha, \mathbb{K})$, the functional $\varphi_u$ on $\ell^p$ has the norm
$\|\varphi_u\| = \|u\|_q$. This is the norm identity of Proposition 11.18 of
[brezis2011functional].

Hölder's inequality gives $\le$. The finite-section estimate `lp.sum_norm_rpow_apply_single_le`
gives $\ge$ when $q < \infty$, and the test on the unit vectors gives it when $q = \infty$. -/
theorem norm_toDualCLM_apply (u : lp (fun _ : α => 𝕜) q) : ‖toDualCLM 𝕜 α p q u‖ = ‖u‖ := by
  classical
  refine le_antisymm ?_ ?_
  · have := (toDualCLM 𝕜 α p q).le_of_opNorm_le (norm_toDualCLM_le 𝕜 α p q) u
    rwa [one_mul] at this
  rcases eq_or_ne q ∞ with rfl | hq
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun k => ?_
    have := (toDualCLM 𝕜 α p ∞ u).le_opNorm (lp.single p k 1)
    rwa [toDualCLM_single, mul_one, lp.norm_single (zero_lt_one.trans_le Fact.out), norm_one,
      mul_one] at this
  · have hQ : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
    refine lp.norm_le_of_forall_sum_le hQ (norm_nonneg _) fun s => ?_
    have := sum_norm_rpow_apply_single_le hq (toDualCLM 𝕜 α p q u) s
    simpa only [toDualCLM_single, mul_one] using this

variable (𝕜 α p q)

/-- Let $p$ and $q$ be conjugate exponents with $1 \le p, q \le \infty$. The map
$u \mapsto \varphi_u$, with $\varphi_u(x) = \sum_k u_k x_k$, is a linear isometry
$\ell^q(\alpha, \mathbb{K}) \to (\ell^p)^*$, for any index type $\alpha$. This is the isometry
of Proposition 11.18 of [brezis2011functional]. The pairs $(p, q) = (1, \infty)$ and
$(\infty, 1)$ are included. -/
def toDual : lp (fun _ : α => 𝕜) q →ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p) :=
  ⟨(toDualCLM 𝕜 α p q).toLinearMap, norm_toDualCLM_apply⟩

variable {𝕜 α p q}

/-- The linear isometry `lp.toDual` and the bounded linear map `lp.toDualCLM` send $u$ to the same
functional. -/
@[simp]
theorem coe_toDual (u : lp (fun _ : α => 𝕜) q) : toDual 𝕜 α p q u = toDualCLM 𝕜 α p q u :=
  rfl

/-- The functional `lp.toDual` of $u$ is $x \mapsto \sum_k u_k x_k$, the formula of Proposition
11.18 of [brezis2011functional]. -/
theorem toDual_apply (u : lp (fun _ : α => 𝕜) q) (x : lp (fun _ : α => 𝕜) p) :
    toDual 𝕜 α p q u x = ∑' k, u k * x k :=
  rfl

/-- The functional `lp.toDual` of $u$ on a multiple of a unit vector is $\varphi_u(a e_k) = u_k a$.
-/
theorem toDual_single [DecidableEq α] (u : lp (fun _ : α => 𝕜) q) (k : α) (a : 𝕜) :
    toDual 𝕜 α p q u (lp.single p k a) = u k * a :=
  toDualCLM_single u k a

/-- Let $p$ and $q$ be conjugate exponents with $1 \le p < \infty$. Every bounded linear functional
$\varphi$ on $\ell^p(\alpha, \mathbb{K})$ is $\varphi_u$ for some
$u \in \ell^q(\alpha, \mathbb{K})$. This is the existence part of Proposition 11.18 of
[brezis2011functional].

The sequence is $u_k = \varphi(e_k)$, and it lies in $\ell^q$ by the finite-section estimate.
The functionals $\varphi$ and $\varphi_u$ are continuous and agree on the unit vectors, whose
finite linear combinations are dense (`lp.hasSum_single`). -/
theorem toDual_surjective (hp : p ≠ ∞) : Function.Surjective (toDual 𝕜 α p q) := by
  intro φ
  classical
  obtain ⟨v, hv⟩ : ∃ v : α → 𝕜, ∀ k, v k = φ (lp.single p k 1) := ⟨_, fun _ => rfl⟩
  have hv_mem : Memℓp v q := by
    rcases eq_or_ne q ∞ with rfl | hq
    · refine memℓp_infty ⟨‖φ‖, ?_⟩
      rintro _ ⟨k, rfl⟩
      have := φ.le_opNorm (lp.single p k 1)
      rwa [lp.norm_single (zero_lt_one.trans_le Fact.out), norm_one, mul_one, ← hv] at this
    · refine memℓp_gen' (C := ‖φ‖ ^ q.toReal) fun s => ?_
      simp only [hv]
      exact sum_norm_rpow_apply_single_le hq φ s
  refine ⟨⟨v, hv_mem⟩, ?_⟩
  refine lp.ext_continuousLinearMap hp fun k => ContinuousLinearMap.ext fun a => ?_
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rw [coe_toDual, toDualCLM_single]
  have h1 : (lp.single p k a : lp (fun _ : α => 𝕜) p) = a • lp.single p k 1 := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul, mul_comm]
  exact congrArg (fun t => a * t) (hv k)

variable (𝕜 α p q)

/-- Let $p$ and $q$ be conjugate exponents with $1 \le p < \infty$. The map $u \mapsto \varphi_u$ is
an isometric isomorphism $\ell^q(\alpha, \mathbb{K}) \cong (\ell^p)^*$. This is Proposition
11.18 of [brezis2011functional], $(\ell^p)^* = \ell^{p'}$. For $p = 1$ it reads
$(\ell^1)^* = \ell^\infty$. -/
def dualEquiv (hp : p ≠ ∞) : lp (fun _ : α => 𝕜) q ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 α p q) (toDual_surjective hp)

variable {𝕜 α p q}

/-- The isometric isomorphism `lp.dualEquiv` sends $u$ to the functional $x \mapsto \sum_k u_k x_k$.
-/
theorem dualEquiv_apply (hp : p ≠ ∞) (u : lp (fun _ : α => 𝕜) q) (x : lp (fun _ : α => 𝕜) p) :
    dualEquiv 𝕜 α p q hp u x = ∑' k, u k * x k :=
  rfl

/-- The isometric isomorphism `lp.dualEquiv` and the linear isometry `lp.toDual` send $u$ to the
same functional. -/
@[simp]
theorem coe_dualEquiv (hp : p ≠ ∞) (u : lp (fun _ : α => 𝕜) q) :
    dualEquiv 𝕜 α p q hp u = toDual 𝕜 α p q u :=
  rfl

end Duality

/-! ### Reflexivity of $\ell^p$ for $1 < p < \infty$ -/

section Reflexive

variable (𝕜 : Type*) [RCLike 𝕜] (α : Type*) {p : ℝ≥0∞}

/-- For $1 < p < \infty$ and any index type $\alpha$, the space $\ell^p(\alpha, \mathbb{K})$ is
reflexive. This is the reflexivity part of Proposition 11.15 of [brezis2011functional].

The proof uses the duality directly. Let $q$ be the conjugate exponent, and let
$e_p \colon \ell^q \cong (\ell^p)^*$ and $e_q \colon \ell^p \cong (\ell^q)^*$ be the isometries
of Proposition 11.18. A functional $\Phi$ on $(\ell^p)^*$ gives $\Phi \circ e_p = e_q(x)$ for
some $x \in \ell^p$. Then $\Phi(e_p u) = \sum_k u_k x_k = (e_p u)(x)$, so $\Phi$ is the
evaluation at $x$. The source applies Theorem 4.10 to the counting measure instead. -/
theorem isReflexive [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive 𝕜 (lp (fun _ : α => 𝕜) p) := by
  set q := ENNReal.conjExponent p with hq
  have hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent Fact.out
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  set ep := dualEquiv 𝕜 α p q hp' with hep
  set eq := dualEquiv 𝕜 α q p hq' with heq
  refine ⟨fun Φ => ?_⟩
  obtain ⟨x, hx⟩ := eq.surjective (Φ.comp (ep.toContinuousLinearEquiv :
    lp (fun _ : α => 𝕜) q →L[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p)))
  refine ⟨x, ?_⟩
  ext f
  obtain ⟨u, rfl⟩ := ep.surjective f
  have h1 : eq x u = Φ (ep u) := by
    have := DFunLike.congr_fun hx u
    simpa using this
  rw [NormedSpace.dual_def, ← h1, heq, hep, dualEquiv_apply, dualEquiv_apply]
  exact tsum_congr fun k => mul_comm _ _

/-- The space $\ell^p(\alpha, \mathbb{K})$ is reflexive for $1 < p < \infty$, as an instance under
the hypotheses `Fact (1 < p)` and `Fact (p ≠ ∞)`. These are the hypotheses of
`MeasureTheory.Lp.instIsReflexive`. -/
instance instIsReflexive [Fact (1 < p)] [Fact (p ≠ ∞)] :
    NormedSpace.IsReflexive 𝕜 (lp (fun _ : α => 𝕜) p) :=
  isReflexive 𝕜 α Fact.out Fact.out

end Reflexive

/-! ### The dual of $c_0$ -/

section ZeroAtInftyDual

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The scalar $\operatorname{sign}(z) = \overline{z} / |z|$, with $\operatorname{sign}(0) = 0$. It
has norm at most $1$ and satisfies $z \operatorname{sign}(z) = |z|$. -/
private def sgn (z : 𝕜) : 𝕜 := (starRingEnd 𝕜) z / (‖z‖ : 𝕜)

private theorem mul_sgn (z : 𝕜) : z * sgn z = (‖z‖ : 𝕜) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [sgn]
  · rw [sgn, ← mul_div_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_div, pow_two,
      mul_div_assoc, div_self (norm_ne_zero_iff.2 hz), mul_one]

private theorem norm_sgn_le (z : 𝕜) : ‖sgn z‖ ≤ 1 := by
  rw [sgn, norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm]
  exact div_self_le_one _

variable (𝕜)

/-- The unit sequence $e_k$, as an element of $c_0$. -/
private def e₀ (k : ℕ) : zeroAtInfty 𝕜 𝕜 := ⟨lp.single ∞ k 1, single_mem_zeroAtInfty 𝕜 𝕜 k 1⟩

/-- The map that sends $u \in \ell^1(\mathbb{N}, \mathbb{K})$ to the functional
$x \mapsto \sum_k u_k x_k$ on $c_0$, as a bounded linear map $\ell^1 \to (c_0)^*$. It is the
case $(p, q) = (\infty, 1)$ of `lp.toDualCLM`, restricted to $c_0$. -/
def zeroAtInfty.toDualCLM : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) :=
  ((ContinuousLinearMap.compL 𝕜 (zeroAtInfty 𝕜 𝕜) (lp (fun _ : ℕ => 𝕜) ∞) 𝕜).flip
    (zeroAtInfty 𝕜 𝕜).subtypeL).comp (lp.toDualCLM 𝕜 ℕ ∞ 1)

variable {𝕜}

/-- The functional of $u \in \ell^1$ on $c_0$ is $x \mapsto \sum_k u_k x_k$. -/
theorem zeroAtInfty.toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.toDualCLM 𝕜 u x = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
  rfl

/-- The **finite-section estimate for $c_0$**. Let $\varphi$ be a bounded linear functional on
$c_0$, and let $u_k = \varphi(e_k)$. Then $\sum_{k \in s} |u_k| \le \|\varphi\|$ for every
finite set $s \subseteq \mathbb{N}$. This is the estimate in the proof of Proposition 11.19 of
[brezis2011functional].

The proof tests $\varphi$ on the finitely supported sequence with
$x_k = \operatorname{sign}(u_k)$ for $k \in s$, which has norm at most $1$. -/
theorem zeroAtInfty.sum_norm_apply_single_le (φ : StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜))
    (s : Finset ℕ) :
    ∑ k ∈ s, ‖φ ⟨lp.single ∞ k 1, single_mem_zeroAtInfty 𝕜 𝕜 k 1⟩‖ ≤ ‖φ‖ := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ → 𝕜, ∀ k, v k = φ (e₀ 𝕜 k) := ⟨_, fun _ => rfl⟩
  change ∑ k ∈ s, ‖φ (e₀ 𝕜 k)‖ ≤ ‖φ‖
  simp only [← hv]
  set x : zeroAtInfty 𝕜 𝕜 := ⟨∑ k ∈ s, lp.single ∞ k (sgn (v k)),
    Submodule.sum_mem _ fun k _ => single_mem_zeroAtInfty 𝕜 𝕜 k _⟩ with hx
  have hx' : x = ∑ k ∈ s, sgn (v k) • e₀ 𝕜 k := by
    apply Subtype.ext
    rw [hx, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, e₀, ← lp.single_smul, smul_eq_mul, mul_one]
  have hφx : φ x = ((∑ k ∈ s, ‖v k‖ : ℝ) : 𝕜) := by
    have hms : φ (∑ k ∈ s, sgn (v k) • e₀ 𝕜 k) = ∑ k ∈ s, φ (sgn (v k) • e₀ 𝕜 k) :=
      map_sum φ _ _
    rw [hx', hms, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, ← hv, mul_comm, mul_sgn]
  have hx1 : ‖x‖ ≤ 1 := by
    rw [← Submodule.norm_coe]
    refine lp.norm_le_of_forall_le zero_le_one fun j => ?_
    rw [hx]
    change ‖(∑ k ∈ s, lp.single ∞ k (sgn (v k)) : lp (fun _ : ℕ => 𝕜) ∞) j‖ ≤ 1
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_single, Finset.sum_pi_single]
    split_ifs with hj
    · exact norm_sgn_le _
    · rw [_root_.norm_zero]
      exact zero_le_one
  calc ∑ k ∈ s, ‖v k‖ = ‖φ x‖ := by
        rw [hφx, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
    _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    _ ≤ ‖φ‖ * 1 := by gcongr
    _ = ‖φ‖ := mul_one _

/-- The functional of $u \in \ell^1$ on a multiple of a unit vector of $c_0$ is
$\varphi_u(a e_k) = u_k a$. -/
theorem zeroAtInfty.toDualCLM_single (u : lp (fun _ : ℕ => 𝕜) 1) (k : ℕ) (a : 𝕜) :
    zeroAtInfty.toDualCLM 𝕜 u ⟨lp.single ∞ k a, single_mem_zeroAtInfty 𝕜 𝕜 k a⟩ = u k * a :=
  lp.toDualCLM_single u k a

/-- For every $u \in \ell^1(\mathbb{N}, \mathbb{K})$, the functional $\varphi_u$ on $c_0$ has the
norm $\|\varphi_u\| = \|u\|_1$. This is the norm identity of Proposition 11.19 of
[brezis2011functional]. -/
theorem zeroAtInfty.norm_toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) :
    ‖zeroAtInfty.toDualCLM 𝕜 u‖ = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · calc ‖zeroAtInfty.toDualCLM 𝕜 u‖
        = ‖(lp.toDualCLM 𝕜 ℕ ∞ 1 u).comp (zeroAtInfty 𝕜 𝕜).subtypeL‖ := rfl
      _ ≤ ‖lp.toDualCLM 𝕜 ℕ ∞ 1 u‖ * ‖(zeroAtInfty 𝕜 𝕜).subtypeL‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖u‖ * 1 := by
          gcongr
          · exact (lp.norm_toDualCLM_apply u).le
          · exact Submodule.norm_subtypeL_le _
      _ = ‖u‖ := mul_one _
  · have h1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by simp
    refine lp.norm_le_of_forall_sum_le h1 (norm_nonneg _) fun s => ?_
    simp only [ENNReal.toReal_one, Real.rpow_one]
    have := zeroAtInfty.sum_norm_apply_single_le (zeroAtInfty.toDualCLM 𝕜 u) s
    simpa only [zeroAtInfty.toDualCLM_single, mul_one] using this

variable (𝕜)

/-- The map $u \mapsto \varphi_u$, with $\varphi_u(x) = \sum_k u_k x_k$, is a linear isometry
$\ell^1(\mathbb{N}, \mathbb{K}) \to (c_0)^*$. This is the isometry of Proposition 11.19 of
[brezis2011functional]. -/
def zeroAtInfty.toDual : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) :=
  ⟨(zeroAtInfty.toDualCLM 𝕜).toLinearMap, zeroAtInfty.norm_toDualCLM_apply⟩

variable {𝕜}

/-- The linear isometry `lp.zeroAtInfty.toDual` and the bounded linear map
`lp.zeroAtInfty.toDualCLM` send $u$ to the same functional. -/
@[simp]
theorem zeroAtInfty.coe_toDual (u : lp (fun _ : ℕ => 𝕜) 1) :
    zeroAtInfty.toDual 𝕜 u = zeroAtInfty.toDualCLM 𝕜 u :=
  rfl

/-- The functional `lp.zeroAtInfty.toDual` of $u \in \ell^1$ is $x \mapsto \sum_k u_k x_k$ on $c_0$,
the formula of Proposition 11.19 of [brezis2011functional]. -/
theorem zeroAtInfty.toDual_apply (u : lp (fun _ : ℕ => 𝕜) 1) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.toDual 𝕜 u x = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
  rfl

/-- Every bounded linear functional $\varphi$ on $c_0$ is $\varphi_u$ for some
$u \in \ell^1(\mathbb{N}, \mathbb{K})$. This is the existence part of Proposition 11.19 of
[brezis2011functional].

The sequence is $u_k = \varphi(e_k)$, and it lies in $\ell^1$ by the finite-section estimate.
The two functionals agree because every $x \in c_0$ is the sum of the sequences $x_k e_k$
(`lp.zeroAtInfty.hasSum_single'`), that is, because the finitely supported sequences are dense
in $c_0$. -/
theorem zeroAtInfty.toDual_surjective : Function.Surjective (zeroAtInfty.toDual 𝕜) := by
  intro φ
  obtain ⟨v, hv⟩ : ∃ v : ℕ → 𝕜, ∀ k, v k = φ (e₀ 𝕜 k) := ⟨_, fun _ => rfl⟩
  have hv_mem : Memℓp v 1 := by
    refine memℓp_gen' (C := ‖φ‖) fun s => ?_
    simp only [ENNReal.toReal_one, Real.rpow_one, hv]
    exact zeroAtInfty.sum_norm_apply_single_le φ s
  refine ⟨⟨v, hv_mem⟩, ?_⟩
  ext x
  rw [← (zeroAtInfty.hasSum_single' x |>.mapL φ).tsum_eq, zeroAtInfty.coe_toDual,
    zeroAtInfty.toDualCLM_apply]
  refine tsum_congr fun k => ?_
  have h1 : (⟨lp.single ∞ k ((x : lp (fun _ : ℕ => 𝕜) ∞) k), single_mem_zeroAtInfty 𝕜 𝕜 k _⟩ :
      zeroAtInfty 𝕜 𝕜) = (x : lp (fun _ : ℕ => 𝕜) ∞) k • e₀ 𝕜 k := by
    apply Subtype.ext
    rw [Submodule.coe_smul, e₀, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul, ← hv, mul_comm]

variable (𝕜)

/-- The map $u \mapsto \varphi_u$, with $\varphi_u(x) = \sum_k u_k x_k$, is an isometric isomorphism
$\ell^1(\mathbb{N}, \mathbb{K}) \cong (c_0)^*$. This is Proposition 11.19 of
[brezis2011functional], $(c_0)^* = \ell^1$. -/
def zeroAtInfty.dualEquiv : lp (fun _ : ℕ => 𝕜) 1 ≃ₗᵢ[𝕜] StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) :=
  LinearIsometryEquiv.ofSurjective (zeroAtInfty.toDual 𝕜) zeroAtInfty.toDual_surjective

variable {𝕜}

/-- The isometric isomorphism `lp.zeroAtInfty.dualEquiv` sends $u$ to the functional
$x \mapsto \sum_k u_k x_k$ on $c_0$. -/
theorem zeroAtInfty.dualEquiv_apply (u : lp (fun _ : ℕ => 𝕜) 1) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.dualEquiv 𝕜 u x = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
  rfl

/-- The isometric isomorphism `lp.zeroAtInfty.dualEquiv` and the linear isometry
`lp.zeroAtInfty.toDual` send $u$ to the same functional. -/
@[simp]
theorem zeroAtInfty.coe_dualEquiv (u : lp (fun _ : ℕ => 𝕜) 1) :
    zeroAtInfty.dualEquiv 𝕜 u = zeroAtInfty.toDual 𝕜 u :=
  rfl

end ZeroAtInftyDual

/-! ### The dual of $c$ -/

section ConvergentDual

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The map that sends $(u, \lambda) \in \ell^1(\mathbb{N}, \mathbb{K}) \times \mathbb{K}$ to the
functional $\varphi_{u,\lambda}(x) = \sum_k u_k x_k + \lambda \lim x$ on $c$, as a bounded
linear map $\ell^1 \times \mathbb{K} \to c^*$. The product carries the norm
$\|u\|_1 + |\lambda|$: it is `WithLp 1 (lp (fun _ : ℕ ↦ 𝕜) 1 × 𝕜)`. -/
def convergent.toDualCLM :
    WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜) →L[𝕜] StrongDual 𝕜 (convergent 𝕜 𝕜) :=
  (((ContinuousLinearMap.compL 𝕜 (convergent 𝕜 𝕜) (lp (fun _ : ℕ => 𝕜) ∞) 𝕜).flip
      (convergent 𝕜 𝕜).subtypeL).comp (lp.toDualCLM 𝕜 ℕ ∞ 1)).comp
    (WithLp.fstL 1 𝕜 (lp (fun _ : ℕ => 𝕜) 1) 𝕜) +
    (WithLp.sndL 1 𝕜 (lp (fun _ : ℕ => 𝕜) 1) 𝕜).smulRight (convergent.limCLM 𝕜 𝕜)

variable {𝕜}

/-- The functional of $(u, \lambda)$ on $c$ is $\varphi_{u,\lambda}(x) = \sum_k u_k x_k + \lambda
\lim x$. -/
theorem convergent.toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (x : convergent 𝕜 𝕜) :
    convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l)) x =
      ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + l * convergent.limCLM 𝕜 𝕜 x :=
  rfl

/-- In the product $\ell^1 \times \mathbb{K}$ with the $\ell^1$ product norm (`WithLp 1`), the pair
$(u, \lambda)$ has the norm $\|u\|_1 + |\lambda|$. -/
theorem norm_toLp_one_prod (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) :
    ‖(WithLp.toLp 1 (u, l) : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜))‖ = ‖u‖ + ‖l‖ := by
  rw [WithLp.prod_norm_eq_add (by simp)]
  simp

/-- For $u \in \ell^1(\mathbb{N}, \mathbb{K})$ and $x \in \ell^\infty(\mathbb{N}, \mathbb{K})$, the
family $(u_k x_k)_k$ is summable. -/
theorem summable_mul_apply_of_one_of_top (u : lp (fun _ : ℕ => 𝕜) 1)
    (x : lp (fun _ : ℕ => 𝕜) ∞) : Summable fun k => u k * x k := by
  have hsum : Summable fun k => ‖u k‖ := by
    simpa using (lp.memℓp u).summable (p := 1) (by simp)
  refine Summable.of_norm_bounded (g := fun k => ‖u k‖ * ‖x‖) (hsum.mul_right _) fun k => ?_
  rw [norm_mul]
  gcongr
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero x k

/-- The functional $\varphi_{u,\lambda}$ on $c$ has the norm $\|\varphi_{u,\lambda}\| \le \|u\|_1 +
|\lambda|$. This is the easy half of the norm identity of Proposition 11.20 of
[brezis2011functional]. -/
theorem convergent.norm_toDualCLM_apply_le (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) :
    ‖convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l))‖ ≤ ‖u‖ + ‖l‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [convergent.toDualCLM_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k‖
        = ‖lp.toDualCLM 𝕜 ℕ ∞ 1 u (x : lp (fun _ : ℕ => 𝕜) ∞)‖ := rfl
      _ ≤ ‖lp.toDualCLM 𝕜 ℕ ∞ 1 u‖ * ‖(x : lp (fun _ : ℕ => 𝕜) ∞)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖u‖ * ‖x‖ := by rw [lp.norm_toDualCLM_apply, Submodule.norm_coe]
  · rw [norm_mul]
    gcongr
    exact convergent.norm_limCLM_apply_le x

/-- The test sequence of the proof of Proposition 11.20 of [brezis2011functional], as an element of
$\ell^\infty$: its term $k$ is $\operatorname{sign}(u_k)$ for $k < N$ and
$\operatorname{sign}(\lambda)$ for $k \ge N$. -/
private def testFun (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) : lp (fun _ : ℕ => 𝕜) ∞ :=
  ⟨fun k => if k < N then sgn (u k) else sgn l, memℓp_infty ⟨1, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    split_ifs <;> exact norm_sgn_le _⟩⟩

private theorem tendsto_testFun (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) :
    Tendsto (⇑(testFun u l N)) atTop (𝓝 (sgn l)) := by
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
  change sgn l = if k < N then sgn (u k) else sgn l
  rw [ite_eq_right (not_lt.2 hk)]

/-- The test sequence of the proof of Proposition 11.20 of [brezis2011functional], as an element of
$c$. -/
private def testSeq (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) : convergent 𝕜 𝕜 :=
  ⟨testFun u l N, sgn l, tendsto_testFun u l N⟩

private theorem testSeq_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N k : ℕ) :
    ((testSeq u l N : convergent 𝕜 𝕜) : lp (fun _ : ℕ => 𝕜) ∞) k =
      if k < N then sgn (u k) else sgn l :=
  rfl

private theorem norm_testSeq_le (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) :
    ‖testSeq u l N‖ ≤ 1 := by
  rw [← Submodule.norm_coe]
  refine lp.norm_le_of_forall_le zero_le_one fun k => ?_
  rw [testSeq_apply]
  split_ifs <;> exact norm_sgn_le _

private theorem limCLM_testSeq (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) :
    convergent.limCLM 𝕜 𝕜 (testSeq u l N) = sgn l :=
  convergent.limCLM_eq_of_tendsto (tendsto_testFun u l N)

/-- The functional $\varphi_{u,\lambda}$ on $c$ has the norm $\|\varphi_{u,\lambda}\| \ge \|u\|_1 +
|\lambda|$. This is the hard half of the norm identity of Proposition 11.20 of
[brezis2011functional].

The proof tests $\varphi_{u,\lambda}$ on $x_N = (\operatorname{sign} u_0, \dots,
\operatorname{sign} u_{N-1}, \operatorname{sign} \lambda, \operatorname{sign} \lambda, \dots)$.
This gives $\sum_{k < N} |u_k| + |\lambda| - \sum_{k \ge N} |u_k| \le \|\varphi_{u,\lambda}\|$,
and then $N \to \infty$. -/
theorem convergent.norm_add_norm_le_norm_toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) :
    ‖u‖ + ‖l‖ ≤ ‖convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l))‖ := by
  set φ := convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l)) with hφ
  have hsum : Summable fun k => ‖u k‖ := by
    simpa using (lp.memℓp u).summable (p := 1) (by simp)
  -- the estimate at a fixed `N`
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ - ∑' k, ‖u (k + N)‖ ≤ ‖φ‖ := by
    intro N
    obtain ⟨x, hx⟩ : ∃ x, x = testSeq u l N := ⟨_, rfl⟩
    have hlim : convergent.limCLM 𝕜 𝕜 x = sgn l := by rw [hx]; exact limCLM_testSeq u l N
    have hx1 : ‖x‖ ≤ 1 := by rw [hx]; exact norm_testSeq_le u l N
    have hφx : φ x = ((∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ : ℝ) : 𝕜) +
        ∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N) := by
      rw [hφ, convergent.toDualCLM_apply, hlim, mul_sgn,
        ← (summable_mul_apply_of_one_of_top u x).sum_add_tsum_nat_add N]
      have : ∑ k ∈ Finset.range N, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k =
          ((∑ k ∈ Finset.range N, ‖u k‖ : ℝ) : 𝕜) := by
        rw [RCLike.ofReal_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hx, testSeq_apply, ite_eq_left (Finset.mem_range.1 hk), mul_sgn]
      rw [this]
      push_cast
      ring
    have htail : ‖∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ ≤ ∑' k, ‖u (k + N)‖ := by
      have hs1 : Summable fun k => ‖u (k + N)‖ := (summable_nat_add_iff N).2 hsum
      have hs2 : Summable fun k => u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N) :=
        (summable_nat_add_iff N).2 (summable_mul_apply_of_one_of_top u x)
      have hxk : ∀ k, ‖(x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ ≤ 1 := fun k => by
        rw [hx, testSeq_apply]
        split_ifs <;> exact norm_sgn_le _
      have hle : ∀ k, ‖u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ ≤ ‖u (k + N)‖ :=
        fun k => by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hxk k)
      calc ‖∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖
          ≤ ∑' k, ‖u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ :=
            norm_tsum_le_tsum_norm hs2.norm
        _ ≤ ∑' k, ‖u (k + N)‖ := Summable.tsum_le_tsum hle hs2.norm hs1
    have hnn : 0 ≤ ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ := by positivity
    calc ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ - ∑' k, ‖u (k + N)‖
        ≤ ‖((∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ : ℝ) : 𝕜)‖ -
          ‖∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ := by
          rw [RCLike.norm_ofReal, abs_of_nonneg hnn]
          exact sub_le_sub_left htail _
      _ ≤ ‖φ x‖ := by
          rw [hφx]
          exact sub_le_iff_le_add.2 (norm_le_add_norm_add _ _)
      _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hx1 (norm_nonneg _)
      _ = ‖φ‖ := mul_one _
  -- let `N → ∞`
  have h1 : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖u k‖) atTop (𝓝 ‖u‖) := by
    have := (lp.hasSum_norm (p := 1) (by simp) u).tendsto_sum_nat
    simpa using this
  have h2 : Tendsto (fun N => ∑' k, ‖u (k + N)‖) atTop (𝓝 0) :=
    tendsto_sum_nat_add fun k => ‖u k‖
  have h3 : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ - ∑' k, ‖u (k + N)‖) atTop
      (𝓝 (‖u‖ + ‖l‖ - 0)) := (h1.add_const _).sub h2
  rw [sub_zero] at h3
  exact le_of_tendsto' h3 key

/-- For every $w = (u, \lambda)$ in $\ell^1(\mathbb{N}, \mathbb{K}) \times \mathbb{K}$ with the norm
$\|u\|_1 + |\lambda|$, the functional $\varphi_w$ on $c$ has the norm $\|\varphi_w\| = \|w\|$.
This is the norm identity of Proposition 11.20 of [brezis2011functional]. -/
theorem convergent.norm_toDualCLM_apply (w : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜)) :
    ‖convergent.toDualCLM 𝕜 w‖ = ‖w‖ := by
  obtain ⟨⟨u, l⟩⟩ := w
  rw [norm_toLp_one_prod]
  exact le_antisymm (convergent.norm_toDualCLM_apply_le u l)
    (convergent.norm_add_norm_le_norm_toDualCLM_apply u l)

variable (𝕜)

/-- The map $(u, \lambda) \mapsto \varphi_{u,\lambda}$, with $\varphi_{u,\lambda}(x) = \sum_k u_k
x_k + \lambda \lim x$, is a linear isometry from $\ell^1(\mathbb{N}, \mathbb{K}) \times
\mathbb{K}$, with the norm $\|u\|_1 + |\lambda|$, to $c^*$. This is the isometry of Proposition
11.20 of [brezis2011functional]. -/
def convergent.toDual : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜) →ₗᵢ[𝕜] StrongDual 𝕜 (convergent 𝕜 𝕜) :=
  ⟨(convergent.toDualCLM 𝕜).toLinearMap, convergent.norm_toDualCLM_apply⟩

variable {𝕜}

/-- The linear isometry `lp.convergent.toDual` and the bounded linear map `lp.convergent.toDualCLM`
send $(u, \lambda)$ to the same functional. -/
@[simp]
theorem convergent.coe_toDual (w : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜)) :
    convergent.toDual 𝕜 w = convergent.toDualCLM 𝕜 w :=
  rfl

/-- The functional `lp.convergent.toDual` of $(u, \lambda)$ is
$x \mapsto \sum_k u_k x_k + \lambda \lim x$, the formula of Proposition 11.20 of
[brezis2011functional]. -/
theorem convergent.toDual_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (x : convergent 𝕜 𝕜) :
    convergent.toDual 𝕜 (WithLp.toLp 1 (u, l)) x =
      ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + l * convergent.limCLM 𝕜 𝕜 x :=
  rfl

/-- The inclusion $c_0 \to c$, as a bounded linear map. -/
private def incl : zeroAtInfty 𝕜 𝕜 →L[𝕜] convergent 𝕜 𝕜 :=
  (Submodule.inclusion (zeroAtInfty_le_convergent 𝕜 𝕜)).mkContinuous 1 fun x => by
    rw [one_mul, ← Submodule.norm_coe, ← Submodule.norm_coe (s := zeroAtInfty 𝕜 𝕜)]
    rfl

/-- Every bounded linear functional $\varphi$ on $c$ is $\varphi_{u,\lambda}$ for some
$u \in \ell^1(\mathbb{N}, \mathbb{K})$ and $\lambda \in \mathbb{K}$. This is the existence part
of Proposition 11.20 of [brezis2011functional].

The restriction of $\varphi$ to $c_0$ gives $u \in \ell^1$ with $\varphi(y) = \sum_k u_k y_k$
for $y \in c_0$. Let $e = (1, 1, 1, \dots)$ and $\lambda = \varphi(e) - \sum_k u_k$. Every
$x \in c$ is $y + (\lim x) e$ with $y \in c_0$, so
$\varphi(x) = \sum_k u_k x_k + \lambda \lim x$. -/
theorem convergent.toDual_surjective : Function.Surjective (convergent.toDual 𝕜) := by
  intro φ
  set u := (zeroAtInfty.dualEquiv 𝕜).symm (φ.comp incl) with hu
  have hu' : ∀ y : zeroAtInfty 𝕜 𝕜, φ (incl y) = ∑' k, u k * (y : lp (fun _ : ℕ => 𝕜) ∞) k := by
    intro y
    have := DFunLike.congr_fun ((zeroAtInfty.dualEquiv 𝕜).apply_symm_apply (φ.comp incl)) y
    rw [← hu, zeroAtInfty.dualEquiv_apply] at this
    rw [this]
    rfl
  set e : convergent 𝕜 𝕜 := ⟨constL 𝕜 𝕜 1, constL_mem_convergent 𝕜 𝕜 1⟩ with he
  refine ⟨WithLp.toLp 1 (u, φ e - ∑' k, u k), ?_⟩
  ext x
  rw [convergent.coe_toDual, convergent.toDualCLM_apply]
  set a := convergent.limCLM 𝕜 𝕜 x with ha
  -- `x = y + a • e` with `y ∈ c₀`
  set y : zeroAtInfty 𝕜 𝕜 := ⟨(x : lp (fun _ : ℕ => 𝕜) ∞) - constL 𝕜 𝕜 a,
    convergent.sub_constL_limCLM_mem_zeroAtInfty x⟩ with hy
  have hxy : x = incl y + a • e := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, he]
    change (x : lp (fun _ : ℕ => 𝕜) ∞) = ((x : lp (fun _ : ℕ => 𝕜) ∞) - constL 𝕜 𝕜 a) +
      a • constL 𝕜 𝕜 1
    rw [← map_smul, smul_eq_mul, mul_one, sub_add_cancel]
  have hsum : Summable fun k => u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
    summable_mul_apply_of_one_of_top u x
  have hsum' : Summable fun k => u k * a := by
    simpa using summable_mul_apply_of_one_of_top u (constL 𝕜 𝕜 a)
  symm
  calc φ x = φ (incl y) + a * φ e := by rw [hxy, map_add, map_smul, smul_eq_mul]
    _ = ∑' k, u k * ((x : lp (fun _ : ℕ => 𝕜) ∞) k - a) + a * φ e := by
        rw [hu' y]
        rfl
    _ = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k - a * ∑' k, u k + a * φ e := by
        simp_rw [mul_sub]
        rw [hsum.tsum_sub hsum', tsum_mul_right, mul_comm a, mul_comm _ a]
    _ = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + (φ e - ∑' k, u k) * a := by ring

variable (𝕜)

/-- The map $(u, \lambda) \mapsto \varphi_{u,\lambda}$, with $\varphi_{u,\lambda}(x) = \sum_k u_k
x_k + \lambda \lim x$, is an isometric isomorphism from $\ell^1(\mathbb{N}, \mathbb{K}) \times
\mathbb{K}$, with the norm $\|u\|_1 + |\lambda|$, onto $c^*$. This is Proposition 11.20 of
[brezis2011functional], $c^* = \ell^1 \times \mathbb{K}$. -/
def convergent.dualEquiv :
    WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (convergent 𝕜 𝕜) :=
  LinearIsometryEquiv.ofSurjective (convergent.toDual 𝕜) convergent.toDual_surjective

variable {𝕜}

/-- The isometric isomorphism `lp.convergent.dualEquiv` sends $(u, \lambda)$ to the functional
$x \mapsto \sum_k u_k x_k + \lambda \lim x$ on $c$. -/
theorem convergent.dualEquiv_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (x : convergent 𝕜 𝕜) :
    convergent.dualEquiv 𝕜 (WithLp.toLp 1 (u, l)) x =
      ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + l * convergent.limCLM 𝕜 𝕜 x :=
  rfl

/-- The isometric isomorphism `lp.convergent.dualEquiv` and the linear isometry
`lp.convergent.toDual` send $w$ to the same functional. -/
@[simp]
theorem convergent.coe_dualEquiv (w : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜)) :
    convergent.dualEquiv 𝕜 w = convergent.toDual 𝕜 w :=
  rfl

end ConvergentDual

/-! ### Non-reflexivity of $c_0$, $\ell^\infty$, $c$ and $\ell^1$ -/

section NotReflexive

variable (𝕜 : Type*) [RCLike 𝕜]

variable {𝕜} in
/-- Under the isomorphism $\ell^1 \cong (c_0)^*$, the unit sequence $e_k \in \ell^1$ corresponds to
the evaluation $x \mapsto x_k$ at the index $k$. -/
theorem zeroAtInfty.dualEquiv_single_apply (k : ℕ) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.dualEquiv 𝕜 (lp.single 1 k 1) x = (x : lp (fun _ : ℕ => 𝕜) ∞) k := by
  rw [zeroAtInfty.dualEquiv_apply, tsum_eq_single k fun j hj => by
    rw [lp.single_apply, Pi.single_eq_of_ne hj, zero_mul]]
  rw [lp.single_apply, Pi.single_eq_same, one_mul]

/-- The space $c_0$ of scalar null sequences is not reflexive. This is the case of $c_0$ in
Proposition 11.21 of [brezis2011functional].

Under $(c_0)^* = \ell^1$ and $(\ell^1)^* = \ell^\infty$, the canonical injection
$c_0 \to (c_0)^{**}$ is the inclusion $c_0 \to \ell^\infty$, which misses $(1, 1, 1, \dots)$. In
the proof, the functional $\Phi$ on $(c_0)^*$ that sends $\varphi_u$ to $\sum_k u_k$ would be
the evaluation at some $x \in c_0$. Testing $\Phi$ on the functionals $\varphi_{e_k}$ gives
$x_k = 1$ for every $k$, which contradicts $x_k \to 0$. -/
theorem zeroAtInfty.not_isReflexive : ¬ NormedSpace.IsReflexive 𝕜 (zeroAtInfty 𝕜 𝕜) := by
  intro h
  set e := zeroAtInfty.dualEquiv 𝕜 with he
  set Φ : StrongDual 𝕜 (StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜)) :=
    (lp.tsumCLM 𝕜 ℕ 𝕜).comp (e.symm.toContinuousLinearEquiv :
      StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) →L[𝕜] lp (fun _ : ℕ => 𝕜) 1) with hΦ
  obtain ⟨x, hx⟩ :=
    NormedSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := zeroAtInfty 𝕜 𝕜) Φ
  have hk : ∀ k : ℕ, (x : lp (fun _ : ℕ => 𝕜) ∞) k = 1 := by
    intro k
    have := DFunLike.congr_fun hx (e (lp.single 1 k 1))
    rw [NormedSpace.dual_def, hΦ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      lp.tsumCLM_apply, he, zeroAtInfty.dualEquiv_single_apply,
      tsum_eq_single k fun j hj => by rw [lp.single_apply, Pi.single_eq_of_ne hj],
      lp.single_apply, Pi.single_eq_same] at this
    exact this
  have h0 : Tendsto (⇑(x : lp (fun _ : ℕ => 𝕜) ∞)) atTop (𝓝 0) := x.2
  rw [show ⇑(x : lp (fun _ : ℕ => 𝕜) ∞) = fun _ => (1 : 𝕜) from funext hk] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- The space $\ell^\infty(\mathbb{N}, \mathbb{K})$ is not reflexive, because its closed subspace
$c_0$ is not reflexive (Proposition 3.20 of [brezis2011functional]). This is the case of
$\ell^\infty$ in Proposition 11.21 of [brezis2011functional]. -/
theorem not_isReflexive_top : ¬ NormedSpace.IsReflexive 𝕜 (lp (fun _ : ℕ => 𝕜) ∞) := fun _ =>
  zeroAtInfty.not_isReflexive 𝕜
    (NormedSpace.isReflexive_of_isClosed (zeroAtInfty 𝕜 𝕜) (isClosed_zeroAtInfty 𝕜 𝕜))

/-- The space $c$ of convergent scalar sequences is not reflexive, because its closed subspace $c_0$
is not reflexive (Proposition 3.20 of [brezis2011functional]). This is the case of $c$ in
Proposition 11.21 of [brezis2011functional]. -/
theorem convergent.not_isReflexive : ¬ NormedSpace.IsReflexive 𝕜 (convergent 𝕜 𝕜) := by
  intro h
  -- `c₀`, seen inside `c`
  set M : Submodule 𝕜 (convergent 𝕜 𝕜) := (zeroAtInfty 𝕜 𝕜).comap (convergent 𝕜 𝕜).subtype with hM
  have hMc : IsClosed (M : Set (convergent 𝕜 𝕜)) :=
    (isClosed_zeroAtInfty 𝕜 𝕜).preimage continuous_subtype_val
  have hMr : NormedSpace.IsReflexive 𝕜 M := NormedSpace.isReflexive_of_isClosed M hMc
  let e : M ≃ₗᵢ[𝕜] zeroAtInfty 𝕜 𝕜 :=
    { Submodule.comapSubtypeEquivOfLe (zeroAtInfty_le_convergent 𝕜 𝕜) with
      norm_map' := fun _ => rfl }
  exact zeroAtInfty.not_isReflexive 𝕜
    ((NormedSpace.isReflexive_congr e.toContinuousLinearEquiv).1 hMr)

/-- The space $\ell^1(\mathbb{N}, \mathbb{K})$ is not reflexive: otherwise its dual $\ell^\infty$
(Proposition 11.18) would be reflexive too (Corollary 3.21 of [brezis2011functional]). This is
the case of $\ell^1$ in Proposition 11.21 of [brezis2011functional]. -/
theorem not_isReflexive_one : ¬ NormedSpace.IsReflexive 𝕜 (lp (fun _ : ℕ => 𝕜) 1) := by
  intro h
  have h1 : NormedSpace.IsReflexive 𝕜 (StrongDual 𝕜 (lp (fun _ : ℕ => 𝕜) 1)) := inferInstance
  exact not_isReflexive_top 𝕜
    ((NormedSpace.isReflexive_congr
      (dualEquiv 𝕜 ℕ 1 ∞ ENNReal.one_ne_top).toContinuousLinearEquiv).2 h1)

end NotReflexive

/-! ### Separability -/

section Separable

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [SeparableSpace 𝕜]

/-- Let $V$ be a normed space over a separable nontrivially normed field. If a separable subset $s$
of $V$ spans a dense subspace, then $V$ is separable. -/
theorem _root_.TopologicalSpace.separableSpace_of_isSeparable_of_dense_span {V : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] {s : Set V} (hs : IsSeparable s)
    (hd : Dense (Submodule.span 𝕜 s : Set V)) : SeparableSpace V := by
  rw [← isSeparable_univ_iff, ← hd.closure_eq]
  exact hs.span.closure

/-- Let $\alpha$ be a countable index type, let $E$ be a separable normed space over a separable
field, and let $1 \le p < \infty$. Then $\ell^p(\alpha, E)$ is separable. This is the case of
$\ell^p$ in Proposition 11.16 of [brezis2011functional].

The finitely supported sequences are dense (`lp.hasSum_single`), and they are spanned by the
separable set of the families $\delta_i a$, for $i \in \alpha$ and $a \in E$, where $\delta_i a$
is $a$ at index $i$ and $0$ elsewhere. -/
theorem separableSpace {α : Type*} [Countable α] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeparableSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    SeparableSpace (lp (fun _ : α => E) p) := by
  classical
  refine separableSpace_of_isSeparable_of_dense_span (𝕜 := 𝕜)
    (s := ⋃ i, Set.range (lp.single (E := fun _ : α => E) p i)) ?_ ?_
  · refine IsSeparable.iUnion fun i => ?_
    rw [← Set.image_univ]
    exact (IsSeparable.of_separableSpace _).image (lp.isometry_single i).continuous
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun f => ?_)
    refine mem_closure_of_tendsto (lp.hasSum_single hp f) (Eventually.of_forall fun s => ?_)
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If $E$ is a separable normed space over a separable field, then $c_0$ is separable. This is the
case of $c_0$ in Proposition 11.16 of [brezis2011functional].

The finitely supported sequences are dense in $c_0$ (`lp.zeroAtInfty.hasSum_single'`). -/
instance zeroAtInfty.instSeparableSpace [SeparableSpace E] : SeparableSpace (zeroAtInfty 𝕜 E) := by
  refine separableSpace_of_isSeparable_of_dense_span (𝕜 := 𝕜) (s := ⋃ k, Set.range fun a : E =>
    (⟨lp.single ∞ k a, single_mem_zeroAtInfty 𝕜 E k a⟩ : zeroAtInfty 𝕜 E)) ?_ ?_
  · refine IsSeparable.iUnion fun k => ?_
    rw [← Set.image_univ]
    exact (IsSeparable.of_separableSpace _).image
      ((lp.isometry_single (E := fun _ : ℕ => E) (p := ∞) k).continuous.subtype_mk _)
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun x => ?_)
    refine mem_closure_of_tendsto (zeroAtInfty.hasSum_single' x) (Eventually.of_forall fun s => ?_)
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.subset_span (Set.mem_iUnion.2 ⟨k, Set.mem_range_self _⟩)

/-- If $E$ is a separable normed space over a separable field, then $c$ is separable. This is the
case of $c$ in Proposition 11.16 of [brezis2011functional].

Let $e = (1, 1, 1, \dots)$. Every $x \in c$ is $(x - (\lim x) e) + (\lim x) e$ with
$x - (\lim x) e \in c_0$. So the finitely supported sequences and the constant sequences span a
dense subspace of $c$. This is the set $D + \lambda (1, 1, 1, \dots)$ of the source. -/
instance convergent.instSeparableSpace [SeparableSpace E] : SeparableSpace (convergent 𝕜 E) := by
  refine separableSpace_of_isSeparable_of_dense_span (𝕜 := 𝕜) (s := (⋃ k, Set.range fun a : E =>
    (⟨lp.single ∞ k a, zeroAtInfty_le_convergent 𝕜 E (single_mem_zeroAtInfty 𝕜 E k a)⟩ :
      convergent 𝕜 E)) ∪ Set.range fun a : E =>
    (⟨constL 𝕜 E a, constL_mem_convergent 𝕜 E a⟩ : convergent 𝕜 E)) ?_ ?_
  · refine IsSeparable.union (IsSeparable.iUnion fun k => ?_) ?_
    · rw [← Set.image_univ]
      exact (IsSeparable.of_separableSpace _).image
        ((lp.isometry_single (E := fun _ : ℕ => E) (p := ∞) k).continuous.subtype_mk _)
    · rw [← Set.image_univ]
      exact (IsSeparable.of_separableSpace _).image ((constL 𝕜 E).continuous.subtype_mk _)
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun x => ?_)
    set a := convergent.limCLM 𝕜 E x with ha
    set y : lp (fun _ : ℕ => E) ∞ := (x : lp (fun _ : ℕ => E) ∞) - constL 𝕜 E a with hy
    have hy0 : y ∈ zeroAtInfty 𝕜 E := convergent.sub_constL_limCLM_mem_zeroAtInfty x
    refine mem_closure_of_tendsto (b := atTop) (f := fun s : Finset ℕ => ∑ k ∈ s,
      (⟨lp.single ∞ k (y k), zeroAtInfty_le_convergent 𝕜 E (single_mem_zeroAtInfty 𝕜 E k _)⟩ :
        convergent 𝕜 E) + ⟨constL 𝕜 E a, constL_mem_convergent 𝕜 E a⟩) ?_
      (Eventually.of_forall fun s => ?_)
    · refine tendsto_subtype_rng.2 ?_
      have h := (zeroAtInfty.hasSum_single hy0).add_const (constL 𝕜 E a)
      have hyx : y + constL 𝕜 E a = x := by rw [hy, sub_add_cancel]
      rw [hyx] at h
      refine h.congr fun s => ?_
      simp only [Submodule.coe_add, Submodule.coe_sum]
    · refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.subset_span
        (Set.mem_union_left _ (Set.mem_iUnion.2 ⟨k, Set.mem_range_self _⟩))) ?_
      exact Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self _))

/-- Let $\alpha$ be an infinite index type and let $E$ be a normed group with $E \ne \{0\}$. Then
$\ell^\infty(\alpha, E)$ is not separable. This is Proposition 11.17 of [brezis2011functional].

Fix $e \ne 0$ in $E$. The sequences $e \mathbf{1}_A$, for $A \subseteq \alpha$, are pairwise at
distance $\|e\|$. So the open balls of radius $\|e\| / 2$ around them are pairwise disjoint and
nonempty, and a separable space has only countably many such balls
(`Pairwise.countable_of_isOpen_disjoint`). But the set of subsets of $\alpha$ is uncountable, by
Cantor's theorem. -/
theorem not_separableSpace_top {α : Type*} [Infinite α] {E : Type*} [NormedAddCommGroup E]
    [Nontrivial E] : ¬ SeparableSpace (lp (fun _ : α => E) ∞) := by
  intro h
  classical
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  -- the indicator sequences
  set ind : Set α → lp (fun _ : α => E) ∞ := fun A =>
    ⟨fun i => if i ∈ A then e else 0, memℓp_infty ⟨‖e‖, by
      rintro _ ⟨i, rfl⟩
      dsimp only
      split_ifs <;> simp⟩⟩ with hind
  have hdist : ∀ A B, A ≠ B → ‖e‖ ≤ dist (ind A) (ind B) := by
    intro A B hAB
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra h'
      refine hAB (Set.ext fun i => ?_)
      by_contra hi
      exact h' ⟨i, hi⟩
    rw [dist_eq_norm]
    refine le_trans ?_ (lp.norm_apply_le_norm ENNReal.top_ne_zero (ind A - ind B) i)
    rw [lp.coeFn_sub, Pi.sub_apply, hind]
    dsimp only
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB] at hi ⊢
  have hdisj : Pairwise (Function.onFun Disjoint fun A => Metric.ball (ind A) (‖e‖ / 2)) :=
    fun A B hAB => Metric.ball_disjoint_ball (le_of_eq_of_le (add_halves _) (hdist A B hAB))
  have hcount : Countable (Set α) := hdisj.countable_of_isOpen_disjoint
    (fun _ => Metric.isOpen_ball) fun _ => Metric.nonempty_ball.2 (by positivity)
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (Set α)
  exact Function.cantor_injective ((Infinite.natEmbedding α) ∘ g)
    ((Infinite.natEmbedding α).injective.comp hg)

end Separable

/-! ### $\ell^p$ as $L^p$ of the counting measure, and uniform convexity -/

section Count

open MeasureTheory

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Let $P \ge 0$ and let $(f_a)_a$ be a family in $E$ such that the real family $(\|f_a\|^P)_a$ is
summable. Then the sum $\sum_a \|f_a\|^P$ computed in $[0, \infty]$ equals the real sum,
embedded in $[0, \infty]$. -/
theorem tsum_enorm_rpow_eq_ofReal {P : ℝ} (hP : 0 ≤ P) {f : α → E}
    (hf : Summable fun a => ‖f a‖ ^ P) :
    ∑' a, ‖f a‖ₑ ^ P = ENNReal.ofReal (∑' a, ‖f a‖ ^ P) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun a => Real.rpow_nonneg (norm_nonneg _) _) hf]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP, ofReal_norm]

/-- Conversely, if the sum $\sum_a \|f_a\|^P$ computed in $[0, \infty]$ is finite, then the real
family $(\|f_a\|^P)_a$ is summable. -/
theorem summable_norm_rpow_of_tsum_enorm_rpow_ne_top {P : ℝ} {f : α → E}
    (hf : ∑' a, ‖f a‖ₑ ^ P ≠ ∞) : Summable fun a => ‖f a‖ ^ P := by
  have := ENNReal.summable_toReal hf
  refine this.congr fun a => ?_
  rw [← ENNReal.toReal_rpow, toReal_enorm]

/-- If the family $(\|f_a\|)_a$ is bounded above, then the supremum $\sup_a \|f_a\|$ computed in
$[0, \infty]$ equals the real supremum, embedded in $[0, \infty]$. For an empty index type, both
sides are $0$. -/
theorem iSup_enorm_eq_ofReal_iSup {f : α → E} (hf : BddAbove (Set.range fun a => ‖f a‖)) :
    ⨆ a, ‖f a‖ₑ = ENNReal.ofReal (⨆ a, ‖f a‖) := by
  have hbdd : BddAbove (Set.range fun a => ‖f a‖₊) := by
    obtain ⟨C, hC⟩ := hf
    refine ⟨(max C 0).toNNReal, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hC ⟨a, rfl⟩).trans (le_max_left _ _)
  simp_rw [enorm_eq_nnnorm]
  rw [← ENNReal.coe_iSup hbdd,
    show (⨆ a, ‖f a‖) = ((⨆ a, ‖f a‖₊ : ℝ≥0) : ℝ) by rw [NNReal.coe_iSup]; simp_rw [coe_nnnorm],
    ENNReal.ofReal_coe_nnreal]

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Let $\alpha$ be a countable measurable space in which every singleton is measurable, and let
$0 < p < \infty$. For the counting measure, the $L^p$ seminorm of $f \colon \alpha \to E$ is
$(\sum_a \|f_a\|^p)^{1/p}$, computed in $[0, \infty]$. -/
theorem eLpNorm_count_eq_tsum (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    eLpNorm f p (Measure.count : Measure α) = (∑' a, ‖f a‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp .of_discrete,
    lintegral_count]

/-- Let $\alpha$ be a countable measurable space in which every singleton is measurable, and let
$1 \le p \le \infty$. A function $f \colon \alpha \to E$ lies in $\ell^p$ if and only if it lies
in $L^p$ of the counting measure. Both conditions say that $\sum_a \|f_a\|^p$ is finite, or that
$\sup_a \|f_a\|$ is finite when $p = \infty$. -/
theorem memℓp_iff_memLp_count [Fact (1 ≤ p)] (f : α → E) :
    Memℓp f p ↔ MemLp f p (Measure.count : Measure α) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rw [memLp_iff]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [memℓp_infty_iff, eLpNorm_exponent_top .of_discrete, eLpNormEssSup_count]
    constructor
    · intro hf
      rw [iSup_enorm_eq_ofReal_iSup hf]
      exact ENNReal.ofReal_lt_top
    · intro hf
      refine ⟨(⨆ a, ‖f a‖ₑ).toReal, ?_⟩
      rintro _ ⟨a, rfl⟩
      dsimp only
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hf.ne (le_iSup (fun a => ‖f a‖ₑ) a)
  · have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [memℓp_gen_iff hP, eLpNorm_count_eq_tsum hp0 hp,
      ENNReal.rpow_lt_top_iff_of_pos (by positivity)]
    constructor
    · intro hf
      rw [tsum_enorm_rpow_eq_ofReal hP.le hf]
      exact ENNReal.ofReal_lt_top
    · exact fun hf => summable_norm_rpow_of_tsum_enorm_rpow_ne_top hf.ne

/-- Let $\alpha$ be a countable measurable space in which every singleton is measurable, and let
$1 \le p \le \infty$. For $f \in \ell^p(\alpha, E)$, the $L^p$ norm of $f$ for the counting
measure is $\|f\|_p$. -/
theorem toReal_eLpNorm_count [Fact (1 ≤ p)] (f : lp (fun _ : α => E) p) :
    (eLpNorm f p (Measure.count : Measure α)).toReal = ‖f‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top .of_discrete, eLpNormEssSup_count,
      iSup_enorm_eq_ofReal_iSup (lp.memℓp f).bddAbove, lp.norm_eq_ciSup, ENNReal.toReal_ofReal]
    rcases isEmpty_or_nonempty α with hα | hα
    · simp
    · exact le_ciSup_of_le (lp.memℓp f).bddAbove (Classical.arbitrary α) (norm_nonneg _)
  · have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [eLpNorm_count_eq_tsum hp0 hp, tsum_enorm_rpow_eq_ofReal hP.le ((lp.memℓp f).summable hP),
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (tsum_nonneg fun a => by positivity),
      lp.norm_eq_tsum_rpow hP]

end Count

section CountEquiv

open MeasureTheory

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (α : Type*) [MeasurableSpace α]
  [MeasurableSingletonClass α] [Countable α] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The linear isometry $\ell^p(\alpha, E) \to L^p(\alpha, \text{counting measure})$,
$f \mapsto [f]$, for a countable measurable space $\alpha$ in which every singleton is
measurable and for $1 \le p \le \infty$. -/
def lpToLpCount : lp (fun _ : α => E) p →ₗᵢ[𝕜] Lp E p (Measure.count : Measure α) where
  toFun f := ((memℓp_iff_memLp_count f).1 (lp.memℓp f)).toLp f
  map_add' f g := by
    change MemLp.toLp (⇑f + ⇑g) _ = _
    exact MemLp.toLp_add _ _
  map_smul' c f := by
    change MemLp.toLp (c • ⇑f) _ = _
    exact MemLp.toLp_const_smul _ _
  norm_map' f := by
    change ‖MemLp.toLp (⇑f) ((memℓp_iff_memLp_count f).1 (lp.memℓp f))‖ = _
    rw [Lp.norm_toLp]
    exact toReal_eLpNorm_count f

/-- For the counting measure, the class $[f]$ has $f$ itself as its representative function. -/
@[simp]
theorem coeFn_lpToLpCount (f : lp (fun _ : α => E) p) : ⇑(lpToLpCount 𝕜 α E p f) = ⇑f := by
  funext a
  exact Measure.ae_count_iff.1
    (MemLp.coeFn_toLp ((memℓp_iff_memLp_count f).1 (lp.memℓp f))) a

/-- Let $\alpha$ be a countable measurable space in which every singleton is measurable, and let
$1 \le p \le \infty$. Then $f \mapsto [f]$ is an isometric isomorphism $\ell^p(\alpha, E) \cong
L^p(\alpha, \text{counting measure})$. This is the identification that §11.3 of
[brezis2011functional] uses to apply chapter 4 to $\ell^p$: "Theorem 4.8 applied to
$\Omega = \mathbb{N}$ equipped with the counting measure".

For the counting measure, equality almost everywhere is equality, so the inverse sends a class
to its representative function. -/
def lpLIELpCount : lp (fun _ : α => E) p ≃ₗᵢ[𝕜] Lp E p (Measure.count : Measure α) :=
  LinearIsometryEquiv.ofSurjective (lpToLpCount 𝕜 α E p) fun g =>
    ⟨⟨(g : α → E), (memℓp_iff_memLp_count _).2 (Lp.memLp g)⟩, Lp.toLp_coeFn g (Lp.memLp g)⟩

/-- The isometric isomorphism `lp.lpLIELpCount` and the linear isometry `lp.lpToLpCount` send $f$ to
the same class. -/
@[simp]
theorem lpLIELpCount_apply (f : lp (fun _ : α => E) p) :
    lpLIELpCount 𝕜 α E p f = lpToLpCount 𝕜 α E p f :=
  rfl

/-- The class of $f \in \ell^p$ in $L^p$ of the counting measure has $f$ itself as its
representative function. -/
@[simp]
theorem coeFn_lpLIELpCount (f : lp (fun _ : α => E) p) : ⇑(lpLIELpCount 𝕜 α E p f) = ⇑f := by
  rw [lpLIELpCount_apply, coeFn_lpToLpCount]

/-- The $\ell^p$ sequence of a class $g$ in $L^p$ of the counting measure is the representative
function of $g$. -/
@[simp]
theorem coeFn_lpLIELpCount_symm (g : Lp E p (Measure.count : Measure α)) :
    ⇑((lpLIELpCount 𝕜 α E p).symm g) = ⇑g := by
  have h := coeFn_lpLIELpCount 𝕜 α E p ((lpLIELpCount 𝕜 α E p).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

end CountEquiv

section UniformConvex

/-- For a countable index type $\alpha$ and $1 < p < \infty$, the real space
$\ell^p(\alpha, \mathbb{R})$ is uniformly convex. This is the uniform convexity part of
Proposition 11.15 of [brezis2011functional].

The proof follows the source, "Theorem 4.10 and Exercise 4.12 with $\Omega = \mathbb{N}$":
uniform convexity is transported from $L^p$ of the counting measure
(`MeasureTheory.Lp.instUniformConvexSpace`, which uses Clarkson's inequalities) along
`lp.lpLIELpCount`. -/
theorem uniformConvexSpace {α : Type*} [Countable α] {p : ℝ≥0∞} [Fact (1 < p)] [Fact (p ≠ ∞)] :
    UniformConvexSpace (lp (fun _ : α => ℝ) p) := by
  let _ : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact uniformConvexSpace_of_linearIsometryEquiv (lpLIELpCount ℝ α ℝ p)

/-- The real space $\ell^p(\alpha, \mathbb{R})$ is uniformly convex for countable $\alpha$ and
$1 < p < \infty$, as an instance. -/
instance instUniformConvexSpace {α : Type*} [Countable α] {p : ℝ≥0∞} [Fact (1 < p)]
    [Fact (p ≠ ∞)] : UniformConvexSpace (lp (fun _ : α => ℝ) p) :=
  uniformConvexSpace

end UniformConvex

end lp

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Oblique projectors

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A **projector** is
a linear map $P : E \to E$ with $P^2 = P$. For subspaces $K$ and $L$ of $E$, a projector onto $K$
orthogonally to $L$ is a projector with range $K$ and kernel $L^\perp$; for every $x$, the vector
$Px$ is then the unique $y \in K$ with $x - y \perp L$. This file shows that a projector is
determined by its range and its kernel, and that a projector onto $K$ orthogonally to $L$ exists
when $K$ and $L$ are finite-dimensional of equal dimension and $K \cap L^\perp = \{0\}$. For two
families $V = (v_1, \dots, v_k)$ and $W = (w_1, \dots, w_k)$ in $E$ whose cross Gram matrix
$W^H V = (\langle w_i, v_j \rangle)_{i,j}$ is invertible, the matrix form $P = V (W^H V)^{-1} W^H$
is the projector onto $\operatorname{span} V$ orthogonally to $\operatorname{span} W$. For $W = V$
orthonormal it is the orthogonal projection $V V^H$.

For bounded projectors, the file proves that a nonzero projector has norm $1$ if and only if it is
self-adjoint, that is, an orthogonal projection. It also proves **Kato's lemma**:
$\|I - P\| = \|P\|$ for every bounded projector $P \neq 0, I$ [szyld2006many].

## Main definitions

* `LinearMap.crossGram`: the cross Gram matrix $W^H V = (\langle w_i, v_j \rangle)_{i,j}$ of two
  families.
* `LinearMap.obliqueProjectionOfBases`: the linear map $V (W^H V)^{-1} W^H$.

## Main results

* `LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq`: two projectors with the same range and the
  same kernel are equal.
* `LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot`: if $K$ and $L$ are
  finite-dimensional of equal dimension and $K \cap L^\perp = \{0\}$, there is exactly one projector
  with range $K$ and kernel $L^\perp$.
* `LinearMap.obliqueProjectionOfBases_isIdempotentElem`, `LinearMap.range_obliqueProjectionOfBases`
  and `LinearMap.ker_obliqueProjectionOfBases`: if $W^H V$ is invertible, $V (W^H V)^{-1} W^H$ is a
  projector with range $\operatorname{span} V$ and kernel $(\operatorname{span} W)^\perp$.
* `LinearMap.obliqueProjectionOfBases_self_eq_starProjection`: for orthonormal $V$,
  $V (V^H V)^{-1} V^H$ is the orthogonal projection onto $\operatorname{span} V$.
* `ContinuousLinearMap.IsIdempotentElem.norm_eq_one_iff_isSymmetric`: a nonzero bounded projector
  has norm $1$ if and only if it is self-adjoint.
* `ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq`: Kato's lemma, $\|I - P\| = \|P\|$ for a
  bounded projector $P \neq 0, I$.

## Proof outline

Kato's lemma rests on an elementary fact about inner product spaces,
`norm_smul_add_smul_eq_norm_add`: if two vectors are rescaled by real factors $s$ and $t$ with
$st = 1$ so that their norms are exchanged, the norm of their sum does not change. It gives the
estimate `ContinuousLinearMap.norm_le_opNorm_mul_norm_add`: if a bounded operator $Q$ maps $u$ to
$0$ and fixes $v$, then $\|u\| \le \|Q\| \, \|u + v\|$. For $Q = I - P$, $u = Px$ and $v = (I - P)x$
this is $\|Px\| \le \|I - P\| \, \|x\|$, so $\|P\| \le \|I - P\|$. The same argument for $I - P$
gives the reverse inequality.

## Implementation notes

* A projector is a linear map `P` with `IsIdempotentElem P`, and the orthogonal complement $L^\perp$
  is `Lᗮ`.
* The families $V$ and $W$ are indexed by a finite type `ι`. The inverse $(W^H V)^{-1}$ is the
  matrix inverse of Mathlib, which is $0$ for a singular matrix. So
  `LinearMap.obliqueProjectionOfBases` is the zero map when $W^H V$ is singular, and the results
  about it assume `IsUnit (LinearMap.crossGram 𝕜 V W)`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The span of a finite family of vectors is finite-dimensional.

Mathlib has this for a `Finset` (`FiniteDimensional.span_finset`) and as a theorem for a finite
set (`FiniteDimensional.span_of_finite`), but not as an instance for the range of a family. -/
instance Submodule.finiteDimensional_span_range {ι : Type*} [Finite ι] (V : ι → E) :
    FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range V)) :=
  Module.Finite.span_of_finite 𝕜 (Set.finite_range V)

namespace LinearMap

/-- Let $P, Q : E \to E$ be linear projectors, that is, $P^2 = P$ and $Q^2 = Q$. If $P$ and $Q$ have
the same range and the same kernel, then $P = Q$. -/
theorem IsIdempotentElem.ext_of_range_eq_of_ker_eq {P Q : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) (hr : LinearMap.range P = LinearMap.range Q)
    (hk : LinearMap.ker P = LinearMap.ker Q) : P = Q := by
  ext x
  have hmem : x - P x ∈ LinearMap.ker Q := by
    rw [← hk, LinearMap.mem_ker, map_sub,
      (LinearMap.IsIdempotentElem.mem_range_iff hP).1 (LinearMap.mem_range_self P x), sub_self]
  have h2 : Q x = Q (P x) := by
    have h := LinearMap.mem_ker.1 hmem
    rw [map_sub, sub_eq_zero] at h
    exact h
  have h3 : Q (P x) = P x := by
    refine (LinearMap.IsIdempotentElem.mem_range_iff hQ).1 ?_
    rw [← hr]
    exact LinearMap.mem_range_self P x
  rw [h2, h3]

/-- Let $P : E \to E$ be a linear projector with range $K$ and kernel $L^\perp$, for subspaces $K$
and $L$ of $E$. Then for all $x, y \in E$,
$$Px = y \iff y \in K \text{ and } x - y \in L^\perp.$$
So $Px$ is the unique element $y$ of $K$ with $x - y \perp L$. -/
theorem IsIdempotentElem.apply_eq_iff {P : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    {K L : Submodule 𝕜 E} (hr : LinearMap.range P = K) (hk : LinearMap.ker P = Lᗮ) (x y : E) :
    P x = y ↔ y ∈ K ∧ x - y ∈ Lᗮ := by
  constructor
  · rintro rfl
    refine ⟨hr ▸ LinearMap.mem_range_self P x, ?_⟩
    rw [← hk, LinearMap.mem_ker, map_sub,
      (LinearMap.IsIdempotentElem.mem_range_iff hP).1 (LinearMap.mem_range_self P x), sub_self]
  · rintro ⟨hy, hxy⟩
    have hyr : y ∈ LinearMap.range P := by rw [hr]; exact hy
    have hmem : x - y ∈ LinearMap.ker P := by rw [hk]; exact hxy
    have h := LinearMap.mem_ker.1 hmem
    rw [map_sub, (LinearMap.IsIdempotentElem.mem_range_iff hP).1 hyr, sub_eq_zero] at h
    exact h

/-- Let $K$ and $L$ be finite-dimensional subspaces of $E$ with $\dim K = \dim L$ and
$K \cap L^\perp = \{0\}$. Then there is exactly one linear projector $P : E \to E$ with range
$K$ and kernel $L^\perp$.

The theorem gives the existence and uniqueness under the condition $K \cap L^\perp = \{0\}$. The
converse, that the condition is necessary, is not stated here. -/
theorem existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot {K L : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) (hKL : K ⊓ Lᗮ = ⊥) :
    ∃! P : E →ₗ[𝕜] E, IsIdempotentElem P ∧ LinearMap.range P = K ∧ LinearMap.ker P = Lᗮ := by
  set g : E →ₗ[𝕜] L := (L.orthogonalProjectionOnto : E →ₗ[𝕜] L)
  set f : K →ₗ[𝕜] L := g.comp K.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx' : (x : E) ∈ Lᗮ := by
      rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact LinearMap.mem_ker.1 hx
    have hmem : (x : E) ∈ K ⊓ Lᗮ := ⟨x.2, hx'⟩
    rw [hKL] at hmem
    exact Subtype.ext (Submodule.mem_bot 𝕜 |>.1 hmem)
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  set e : K ≃ₗ[𝕜] L := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  set P : E →ₗ[𝕜] E := K.subtype.comp ((e.symm : L →ₗ[𝕜] K).comp g)
  have hPmem : ∀ x, P x ∈ K := fun x => (e.symm (g x)).2
  have hPfix : ∀ y ∈ K, P y = y := by
    intro y hy
    change ((e.symm (g y) : K) : E) = y
    have hfy : g y = e ⟨y, hy⟩ := rfl
    rw [hfy, e.symm_apply_apply]
  have hidem : IsIdempotentElem P := LinearMap.ext fun x => hPfix (P x) (hPmem x)
  have hran : LinearMap.range P = K := by
    refine le_antisymm ?_ fun y hy => ⟨y, hPfix y hy⟩
    rintro _ ⟨x, rfl⟩
    exact hPmem x
  have hker : LinearMap.ker P = Lᗮ := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have h' : e.symm (g x) = 0 := Subtype.ext h
      have hgx : g x = 0 := by simpa using congrArg e h'
      exact Submodule.orthogonalProjectionOnto_eq_zero_iff.1 hgx
    · intro h
      have hgx : g x = 0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 h
      change ((e.symm (g x) : K) : E) = 0
      rw [hgx, map_zero]
      rfl
  refine ⟨P, ⟨hidem, hran, hker⟩, ?_⟩
  rintro Q ⟨hQidem, hQran, hQker⟩
  exact IsIdempotentElem.ext_of_range_eq_of_ker_eq hQidem hidem (hQran.trans hran.symm)
    (hQker.trans hker.symm)

section Bases

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (𝕜)

/-- The **cross Gram matrix** of two families $V = (v_j)_{j \in \iota}$ and
$W = (w_i)_{i \in \iota}$ in $E$, indexed by the same finite set: the matrix
$$W^H V = \bigl(\langle w_i, v_j \rangle\bigr)_{i, j \in \iota}.$$

The inner product is conjugate-linear in its first argument, so the entry $(i, j)$ is
$w_i^H v_j$ when $E = \mathbb{K}^n$. -/
noncomputable def crossGram (V W : ι → E) : Matrix ι ι 𝕜 :=
  Matrix.of fun i j => inner 𝕜 (W i) (V j)

/-- The **oblique projector** $V (W^H V)^{-1} W^H$ of two families $V = (v_j)_{j \in \iota}$ and
$W = (w_i)_{i \in \iota}$ in $E$: the linear map
$$x \mapsto \sum_{j \in \iota} \bigl((W^H V)^{-1} c(x)\bigr)_j \, v_j, \qquad c(x) =
  \bigl(\langle w_i, x \rangle\bigr)_{i \in \iota}.$$

When $W^H V$ is invertible, this is the projector onto $\operatorname{span} V$ orthogonally to
$\operatorname{span} W$. The inverse is the matrix inverse of Mathlib, which is $0$ for a
singular matrix, so the map is $0$ when $W^H V$ is singular. -/
noncomputable def obliqueProjectionOfBases (V W : ι → E) : E →ₗ[𝕜] E where
  toFun x := ∑ j, (crossGram 𝕜 V W)⁻¹.mulVec (fun i => inner 𝕜 (W i) x) j • V j
  map_add' := by
    intro x y
    have h : (fun i => inner 𝕜 (W i) (x + y))
        = (fun i => inner 𝕜 (W i) x) + fun i => inner 𝕜 (W i) y := by
      funext i; simp [inner_add_right]
    simp only [h, Matrix.mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    have h : (fun i => inner 𝕜 (W i) (r • x)) = r • fun i => inner 𝕜 (W i) x := by
      funext i; simp [inner_smul_right]
    simp only [h, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,
      Finset.smul_sum]

variable {𝕜}

/-- The value of `LinearMap.obliqueProjectionOfBases` at $x$ is
$\sum_j ((W^H V)^{-1} c(x))_j \, v_j$. -/
private theorem obliqueProjectionOfBases_apply (V W : ι → E) (x : E) :
    obliqueProjectionOfBases 𝕜 V W x =
      ∑ j, (crossGram 𝕜 V W)⁻¹.mulVec (fun i => inner 𝕜 (W i) x) j • V j := rfl

omit [DecidableEq ι] in
/-- The vector of inner products $(\langle w_i, \sum_k c_k v_k \rangle)_i$ is $(W^H V) c$. -/
private theorem inner_sum_smul (V W : ι → E) (c : ι → 𝕜) :
    (fun i => inner 𝕜 (W i) (∑ k, c k • V k)) = (crossGram 𝕜 V W).mulVec c := by
  funext i
  simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, crossGram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable (V W : ι → E) (hVW : IsUnit (crossGram 𝕜 V W))
include hVW

/-- If $W^H V$ is invertible, the oblique projector fixes every linear combination $\sum_k c_k v_k$.
-/
private theorem apply_sum_smul (c : ι → 𝕜) :
    obliqueProjectionOfBases 𝕜 V W (∑ k, c k • V k) = ∑ k, c k • V k := by
  rw [obliqueProjectionOfBases_apply, inner_sum_smul, Matrix.nonsing_inv_mulVec_mulVec hVW]

/-- If $W^H V$ is invertible, then $\langle w_i, Px \rangle = \langle w_i, x \rangle$ for the
oblique projector $P$, every $x$ and every $i$. -/
private theorem inner_apply_eq (x : E) (i : ι) :
    inner 𝕜 (W i) (obliqueProjectionOfBases 𝕜 V W x) = inner 𝕜 (W i) x := by
  have h := congrFun (inner_sum_smul V W ((crossGram 𝕜 V W)⁻¹.mulVec
    (fun k => inner 𝕜 (W k) x))) i
  rw [obliqueProjectionOfBases_apply, h, Matrix.mulVec_nonsing_inv_mulVec hVW]

/-- Let $V = (v_j)_{j \in \iota}$ and $W = (w_i)_{i \in \iota}$ be finite families in $E$ whose
cross Gram matrix $W^H V$ is invertible. Then $P = V (W^H V)^{-1} W^H$ is a projector:
$P^2 = P$.

The proof uses that $P$ fixes every linear combination of the $v_j$, and that every value of $P$
is such a combination. -/
theorem obliqueProjectionOfBases_isIdempotentElem :
    IsIdempotentElem (obliqueProjectionOfBases 𝕜 V W) := by
  refine LinearMap.ext fun x => ?_
  change obliqueProjectionOfBases 𝕜 V W (obliqueProjectionOfBases 𝕜 V W x) = _
  rw [obliqueProjectionOfBases_apply (x := obliqueProjectionOfBases 𝕜 V W x),
    show (fun i => inner 𝕜 (W i) (obliqueProjectionOfBases 𝕜 V W x))
      = fun i => inner 𝕜 (W i) x from funext fun i => inner_apply_eq V W hVW x i]
  rfl

/-- Let $V = (v_j)_{j \in \iota}$ and $W = (w_i)_{i \in \iota}$ be finite families in $E$ whose
cross Gram matrix $W^H V$ is invertible. Then the range of $V (W^H V)^{-1} W^H$ is
$\operatorname{span} V$, the span of the $v_j$. -/
theorem range_obliqueProjectionOfBases :
    LinearMap.range (obliqueProjectionOfBases 𝕜 V W) = Submodule.span 𝕜 (Set.range V) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [obliqueProjectionOfBases_apply]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun 𝕜 |>.1 hy
    exact ⟨∑ k, c k • V k, apply_sum_smul V W hVW c⟩

/-- Let $V = (v_j)_{j \in \iota}$ and $W = (w_i)_{i \in \iota}$ be finite families in $E$ whose
cross Gram matrix $W^H V$ is invertible. Then the kernel of $V (W^H V)^{-1} W^H$ is
$(\operatorname{span} W)^\perp$: a vector is mapped to $0$ if and only if it is orthogonal to
every $w_i$.

Together with `LinearMap.range_obliqueProjectionOfBases` and
`LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq`, this determines the projector uniquely. -/
theorem ker_obliqueProjectionOfBases :
    LinearMap.ker (obliqueProjectionOfBases 𝕜 V W) = (Submodule.span 𝕜 (Set.range W))ᗮ := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_orthogonal_span_range_iff]
  constructor
  · intro h j
    have hj := inner_apply_eq V W hVW x j
    rw [h, inner_zero_right] at hj
    exact hj.symm
  · intro h
    rw [obliqueProjectionOfBases_apply,
      show (fun i => inner 𝕜 (W i) x) = 0 from funext h, Matrix.mulVec_zero]
    simp

/-- The **Petrov–Galerkin condition**. Let $V = (v_j)_{j \in \iota}$ and $W = (w_i)_{i \in \iota}$
be finite families in $E$ whose cross Gram matrix $W^H V$ is invertible, and let
$P = V (W^H V)^{-1} W^H$. Then for every $x \in E$ the error $x - Px$ is orthogonal to the test
space $\operatorname{span} W$:
$$x - Px \in (\operatorname{span} W)^\perp.$$
-/
theorem sub_obliqueProjectionOfBases_apply_mem_orthogonal (x : E) :
    x - obliqueProjectionOfBases 𝕜 V W x ∈ (Submodule.span 𝕜 (Set.range W))ᗮ := by
  rw [Submodule.mem_orthogonal_span_range_iff]
  intro j
  rw [inner_sub_right, inner_apply_eq V W hVW x j, sub_self]

omit hVW in
/-- Let $V = (v_j)_{j \in \iota}$ be a finite orthonormal family in $E$. Then $V (V^H V)^{-1} V^H$
is the orthogonal projection onto $\operatorname{span} V$.

Here $V^H V = I$, so the projector is $V V^H$. The orthogonal projection is
`Submodule.starProjection` of the span, as a linear map. -/
theorem obliqueProjectionOfBases_self_eq_starProjection (hV : Orthonormal 𝕜 V) :
    obliqueProjectionOfBases 𝕜 V V =
      ((Submodule.span 𝕜 (Set.range V)).starProjection : E →ₗ[𝕜] E) := by
  have hG : crossGram 𝕜 V V = 1 := by
    ext i j
    rw [crossGram, Matrix.of_apply, orthonormal_iff_ite.1 hV i j, Matrix.one_apply]
  have hunit : IsUnit (crossGram 𝕜 V V) := hG ▸ isUnit_one
  refine LinearMap.ext fun x => ?_
  refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [← range_obliqueProjectionOfBases V V hunit]
    exact LinearMap.mem_range_self _ x
  · exact sub_obliqueProjectionOfBases_apply_mem_orthogonal V V hunit x

end Bases

end LinearMap

/-- If $t > 0$, $st = 1$ and $s \|u\| = \|v\|$, then $\|t v\| = \|u\|$. -/
private theorem norm_smul_eq_of_mul_eq_one {s t : ℝ} (ht : 0 < t) (hst : s * t = 1) {u v : E}
    (huv : s * ‖u‖ = ‖v‖) : ‖(t : 𝕜) • v‖ = ‖u‖ := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ht]
  linear_combination (-t) * huv + ‖u‖ * hst

/-- Let $u, v \in E$ and let $s, t$ be real numbers with $s > 0$, $st = 1$ and $s \|u\| = \|v\|$.
Then
$$\|s u + t v\| = \|u + v\|.$$

In words: rescaling two vectors so that their norms are exchanged does not change the norm of
their sum. Indeed $\|su\| = \|v\|$ and $\|tv\| = \|u\|$, and the cross term $\operatorname{Re}
\langle su, tv \rangle = st \operatorname{Re} \langle u, v \rangle$ does not change, so the two
expansions of the squared norm agree term by term. This is the geometric fact behind Kato's
lemma `ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq`. -/
theorem norm_smul_add_smul_eq_norm_add {s t : ℝ} (hs : 0 < s) (hst : s * t = 1) (u v : E)
    (huv : s * ‖u‖ = ‖v‖) : ‖(s : 𝕜) • u + (t : 𝕜) • v‖ = ‖u + v‖ := by
  have ht : 0 < t := by nlinarith
  have hnu : ‖(s : 𝕜) • u‖ = ‖v‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hs, huv]
  have hnv : ‖(t : 𝕜) • v‖ = ‖u‖ := norm_smul_eq_of_mul_eq_one ht hst huv
  have hcross : RCLike.re (inner 𝕜 ((s : 𝕜) • u) ((t : 𝕜) • v)) = RCLike.re (inner 𝕜 u v) := by
    rw [inner_smul_left, inner_smul_right, RCLike.conj_ofReal, ← mul_assoc, ← RCLike.ofReal_mul,
      hst, RCLike.ofReal_one, one_mul]
  have hsq : ‖(s : 𝕜) • u + (t : 𝕜) • v‖ ^ 2 = ‖u + v‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜), hnu, hnv, hcross]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 hsq

namespace ContinuousLinearMap

/-- If a bounded operator $P$ has norm $1$, $Py = y$ and $Pz = 0$, then $\langle y, z \rangle = 0$.
-/
private theorem inner_eq_zero_of_norm_eq_one {P : E →L[𝕜] E} (hnorm : ‖P‖ = 1) {y z : E}
    (hy : P y = y) (hz : P z = 0) : inner 𝕜 y z = (0 : 𝕜) := by
  rcases eq_or_ne z 0 with rfl | hzne
  · simp
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hzne) 2
  set c : 𝕜 := inner 𝕜 y z
  set θ : ℝ := -(‖z‖ ^ 2)⁻¹ with hθ
  set t : 𝕜 := (θ : 𝕜) * (starRingEnd 𝕜) c with ht
  have hPyz : P (y + t • z) = y := by
    rw [map_add, map_smul, hy, hz, smul_zero, add_zero]
  have hle : ‖y‖ ≤ ‖y + t • z‖ := by
    calc ‖y‖ = ‖P (y + t • z)‖ := by rw [hPyz]
      _ ≤ ‖P‖ * ‖y + t • z‖ := P.le_opNorm _
      _ = ‖y + t • z‖ := by rw [hnorm, one_mul]
  have hre : RCLike.re (inner 𝕜 y (t • z)) = θ * ‖c‖ ^ 2 := by
    rw [inner_smul_right, ht, mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow,
      RCLike.re_ofReal_mul, RCLike.ofReal_re]
  have hnt : ‖t • z‖ ^ 2 = θ ^ 2 * ‖c‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_smul, ht, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj, mul_pow, mul_pow, sq_abs]
  have hexp : ‖y + t • z‖ ^ 2 = ‖y‖ ^ 2 + 2 * (θ * ‖c‖ ^ 2) + θ ^ 2 * ‖c‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := 𝕜), hre, hnt]
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hsq : ‖y‖ ^ 2 ≤ ‖y + t • z‖ ^ 2 := by nlinarith [norm_nonneg (y + t • z)]
  rw [hexp] at hsq
  have hθz : θ * ‖z‖ ^ 2 = -1 := by
    rw [hθ, neg_mul, inv_mul_cancel₀ hz2.ne']
  have hθneg : θ < 0 := by rw [hθ]; simpa using inv_pos.2 hz2
  have hid : θ ^ 2 * ‖c‖ ^ 2 * ‖z‖ ^ 2 = -(θ * ‖c‖ ^ 2) := by
    rw [show θ ^ 2 * ‖c‖ ^ 2 * ‖z‖ ^ 2 = θ * ‖z‖ ^ 2 * (θ * ‖c‖ ^ 2) by ring, hθz, neg_one_mul]
  have hcsq : ‖c‖ ^ 2 ≤ 0 := by nlinarith
  have hc0 : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
  exact norm_eq_zero.1 hc0

/-- Let $P : E \to E$ be a bounded linear projector with $P \neq 0$. Then $\|P\| = 1$ if and only if
$P$ is self-adjoint, that is, $\langle Px, y \rangle = \langle x, Py \rangle$ for all
$x, y \in E$.

A self-adjoint projector is the orthogonal projection onto its range. -/
theorem IsIdempotentElem.norm_eq_one_iff_isSymmetric {P : E →L[𝕜] E} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) : ‖P‖ = 1 ↔ (P : E →ₗ[𝕜] E).IsSymmetric := by
  have hPP : ∀ x : E, P (P x) = P x := fun x => DFunLike.congr_fun hP x
  constructor
  · intro hnorm x y
    have h1 : inner 𝕜 (P x) (y - P y) = (0 : 𝕜) :=
      inner_eq_zero_of_norm_eq_one hnorm (hPP x) (by rw [map_sub, hPP, sub_self])
    have h2 : inner 𝕜 (P y) (x - P x) = (0 : 𝕜) :=
      inner_eq_zero_of_norm_eq_one hnorm (hPP y) (by rw [map_sub, hPP, sub_self])
    have e1 : inner 𝕜 (P x) y = inner 𝕜 (P x) (P y) := by
      rw [← sub_eq_zero, ← inner_sub_right]; exact h1
    have e2 : inner 𝕜 x (P y) = inner 𝕜 (P x) (P y) := by
      rw [← sub_eq_zero, ← inner_sub_left, ← inner_conj_symm, h2, map_zero]
    exact e1.trans e2.symm
  · intro hsym
    refine le_antisymm (P.opNorm_le_bound zero_le_one fun x => ?_)
      (one_le_norm_of_isIdempotentElem hP h0)
    rw [one_mul]
    have hsq : ‖P x‖ ^ 2 = RCLike.re (inner 𝕜 x (P x)) := by
      have h : inner 𝕜 ((P : E →ₗ[𝕜] E) x) (P x) = inner 𝕜 x ((P : E →ₗ[𝕜] E) (P x)) :=
        hsym x (P x)
      simp only [ContinuousLinearMap.coe_coe, hPP] at h
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), h]
    have hcs : RCLike.re (inner 𝕜 x (P x)) ≤ ‖x‖ * ‖P x‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    nlinarith [norm_nonneg (P x), norm_nonneg x]

/-- The estimate of `ContinuousLinearMap.norm_le_opNorm_mul_norm_add`, with the two rescaling
factors $s$ and $t$ given as hypotheses: if $s > 0$, $st = 1$, $s \|u\| = \|v\|$, $Qu = 0$ and
$Qv = v$, then $\|u\| \le \|Q\| \, \|u + v\|$. -/
private theorem norm_le_opNorm_mul_norm_add_aux {Q : E →L[𝕜] E} {s t : ℝ} (hs : 0 < s)
    (hst : s * t = 1) {u v : E} (huv : s * ‖u‖ = ‖v‖) (hQu : Q u = 0) (hQv : Q v = v) :
    ‖u‖ ≤ ‖Q‖ * ‖u + v‖ := by
  have ht : 0 < t := by nlinarith
  have hQy : Q ((s : 𝕜) • u + (t : 𝕜) • v) = (t : 𝕜) • v := by
    rw [map_add, map_smul, map_smul, hQu, hQv, smul_zero, zero_add]
  calc ‖u‖ = ‖Q ((s : 𝕜) • u + (t : 𝕜) • v)‖ := by
        rw [hQy, norm_smul_eq_of_mul_eq_one ht hst huv]
    _ ≤ ‖Q‖ * ‖(s : 𝕜) • u + (t : 𝕜) • v‖ := Q.le_opNorm _
    _ = ‖Q‖ * ‖u + v‖ := by rw [norm_smul_add_smul_eq_norm_add hs hst u v huv]

/-- Let $Q : E \to E$ be a bounded linear operator, and let $u, v \in E$ be nonzero with $Qu = 0$
and $Qv = v$. Then
$$\|u\| \le \|Q\| \, \|u + v\|.$$

This holds although $Q(u + v) = v$ carries no information about $u$. The proof applies $Q$ to
the rescaled vector $(\|v\| / \|u\|) u + (\|u\| / \|v\|) v$. By `norm_smul_add_smul_eq_norm_add`
this vector has norm $\|u + v\|$, and its image under $Q$ has norm $\|u\|$. -/
theorem norm_le_opNorm_mul_norm_add {Q : E →L[𝕜] E} {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hQu : Q u = 0) (hQv : Q v = v) : ‖u‖ ≤ ‖Q‖ * ‖u + v‖ := by
  have ha : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have hb : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine norm_le_opNorm_mul_norm_add_aux (t := ‖u‖ / ‖v‖)
    (div_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hu)) ?_ ?_ hQu hQv
  · field_simp
  · field_simp

/-- A bounded linear projector $P \neq I$ satisfies $\|P\| \le \|I - P\|$. -/
private theorem norm_le_norm_one_sub {P : E →L[𝕜] E} (hP : IsIdempotentElem P) (h1 : P ≠ 1) :
    ‖P‖ ≤ ‖1 - P‖ := by
  refine P.opNorm_le_bound (norm_nonneg _) fun x => ?_
  have hPP : P (P x) = P x := DFunLike.congr_fun hP x
  have hsum : P x + (1 - P) x = x := by
    rw [sub_apply, one_apply_eq_self]
    abel
  rcases eq_or_ne (P x) 0 with hu | hu
  · rw [hu, norm_zero]
    positivity
  rcases eq_or_ne ((1 - P) x) 0 with hv | hv
  · have hQ0 : (1 : E →L[𝕜] E) - P ≠ 0 := fun h => h1 (sub_eq_zero.1 h).symm
    have hx : P x = x := by
      conv_rhs => rw [← hsum]
      rw [hv, add_zero]
    rw [hx]
    exact le_mul_of_one_le_left (norm_nonneg x)
      (one_le_norm_of_isIdempotentElem hP.one_sub hQ0)
  · have hQu : (1 - P) (P x) = 0 := by rw [sub_apply, one_apply_eq_self, hPP, sub_self]
    have hQv : (1 - P) ((1 - P) x) = (1 - P) x := DFunLike.congr_fun hP.one_sub x
    calc ‖P x‖ ≤ ‖1 - P‖ * ‖P x + (1 - P) x‖ := norm_le_opNorm_mul_norm_add hu hv hQu hQv
      _ = ‖1 - P‖ * ‖x‖ := by rw [hsum]

/-- **Kato's lemma**. Let $P : E \to E$ be a bounded linear projector on an inner product space $E$,
with $P \neq 0$ and $P \neq I$. Then
$$\|I - P\| = \|P\|.$$
See [szyld2006many].

The proof applies `ContinuousLinearMap.norm_le_opNorm_mul_norm_add` with $Q = I - P$ to the
decomposition $x = Px + (I - P)x$. This gives $\|Px\| \le \|I - P\| \, \|x\|$, so
$\|P\| \le \|I - P\|$. The reverse inequality is the same statement for $I - P$. -/
theorem IsIdempotentElem.norm_one_sub_eq {P : E →L[𝕜] E} (hP : IsIdempotentElem P) (h0 : P ≠ 0)
    (h1 : P ≠ 1) : ‖1 - P‖ = ‖P‖ := by
  have hQ1 : (1 : E →L[𝕜] E) - P ≠ 1 := fun h => h0 (sub_eq_self.1 h)
  have h := norm_le_norm_one_sub hP.one_sub hQ1
  rw [sub_sub_cancel] at h
  exact le_antisymm h (norm_le_norm_one_sub hP h1)

end ContinuousLinearMap

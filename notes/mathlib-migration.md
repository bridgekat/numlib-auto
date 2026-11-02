# Mathlib migration: v4.35.0-rc2 → v4.36.0-rc2

The record of the toolchain and Mathlib bump of 2026-11-02 (Mathlib `0653561` → `9d581df`, about
1450 upstream commits), what broke in this library and why, and the proof-writing habits that the
breakage argues for. Read §2 before writing proofs that are meant to survive the next bump; read §1
when doing the next bump.

## 1. What changed and what it cost

245 Lean files changed. Nine full builds were needed to reach a clean build (plus retries after
out-of-memory failures), because an error in one module hides the errors of everything downstream
of it. Almost all of the work came from three upstream changes.

| category | upstream cause | sites | fix |
|---|---|---|---|
| Protected `Matrix` lemmas | Mathlib added generic root lemmas `mul_apply`, `one_apply`, `add_apply`, `sub_apply`, `neg_apply`, `smul_apply`, `zero_apply`, … for any `FunLike` with an `Is*Apply` instance (`Mathlib/Algebra/Group/IsApply.lean`), and made `Matrix.mul_apply`, `Matrix.one_apply`, `Matrix.{add,sub,neg,smul,zero,sum,natCast,intCast}_apply` (and the same names in `CauSeq`, `Derivation`) `protected` | ~875 in ~150 files | qualify as `Matrix.mul_apply` etc. Under `open Matrix` or `namespace Matrix` the bare name now resolves to the root lemma, which does not apply to a matrix: the symptom is ``rewrite failed … (?f * ?g) ?x`` / ``1 ?x`` with "function expected", or `failed to synthesize IsMulApply ?m` |
| `Set` is a structure | `Set α` is now `structure Set (α) where ofPred :: Mem : α → Prop`, no longer `α → Prop`; `setOf` became `Set.ofPred` | ~55 | see §2.2–2.5 |
| `MeasurableSet` → `NullMeasurableSet` | ~30 lemmas were generalised to take `NullMeasurableSet s μ`: `eLpNorm_indicator_eq_eLpNorm_restrict`, `memLp_indicator_iff_restrict`, `indicator_ae_eq_restrict(_compl)`, `eLpNorm_indicator_le`, `memLp_indicator_const`, `MemLp.indicator`, `MemLp.eLpNorm_indicator_le`, `integrableOn_indicator_iff`, `restrict_apply_eq_zero`, … | ~90 | append `.nullMeasurableSet` to the argument |
| `noncomputable` set-valued definitions | a `def … : Set X` is now compiled code, so it fails if its body mentions anything noncomputable (`PiLp` instances, `gradient`, `Measure.restrict`, `supportFn`, a `noncomputable def`) | 24 | mark the definition `noncomputable` |
| Deprecations | `Matrix.linearIndependent_{rows,cols}_iff_isUnit` → `…_{row,col}_iff_isUnit`; `isLowerSet_Iic` → `IsLowerSet.Iic`; `Matrix.norm_entry_le_entrywise_sup_norm` → `Matrix.norm_apply_le_norm`; `Polynomial.trailingCoeff_nonzero_iff_nonzero` → `trailingCoeff_ne_zero`; `BoundedContinuousFunction.{add,sub,smul}_apply` → root lemmas, `…coe_{add,sub,zero}` → `FunLike.coe_*`; `IsAlgClosed.exists_eq_mul_self` → `isSquare`; `ENNReal.tsum_le_tsum` → `tsum_le_tsum`; `finrank_eq_one_iff_of_nonzero'` → `…_of_ne_zero'`; `HasFPowerSeriesAt.has_fpower_series_dslope_fslope` → `dslope_fslope`; `chebyshevTsequence` → `chebyshevTSequence`; `Measure.QuasiMeasurePreserving` → `MeasureTheory.QuasiMeasurePreserving` | 45 | rename |
| Moved modules | `…Integrals.LogTrigonometric` → `…Integrals.Log`, `…Integrability.LogMeromorphic` → `…Integrability.Log`, `ContinuousLinearEquiv.prodCongr` split into `Mathlib.Topology.Algebra.Module.Equiv.Prod`, `Mathlib.Data.Nat.SuccPred` → `Mathlib.Order.SuccPred.Nat`, `Mathlib.Data.Sum.Order` → `Mathlib.Order.Sum.Order`, `…Euclidean.Incenter` → `…Incenter.Basic` | 7 | fix the import |
| Changed signatures | `Function.ExtendByZero.linearMap R M s` (new explicit `M`); `natDegree_X_pow_sub_C (a)` (now explicit, was `{r}`); `tendstoUniformlyOn_of_ae_tendsto'` (takes `AEStronglyMeasurable` and no `hg`); `contDiff_apply 𝕜 F' i` (dependent `F'`); `gramSchmidt_def''` (one implicit fewer) | 12 | adapt the call |
| Tactic behaviour | `gcongr` no longer discharges a positivity side goal from a hypothesis about a folded definition (2); `positivity` likewise (2); the `continuity` auto-param of `ContinuousLinearMap.mk` no longer proves `Continuous (Matrix.mulVecLin A)` (2); `convert` now descends through `Set.ofPred` (1); `rw` closes a goal by `rfl` where it did not before (1) | 8 | see §2.6–2.8 |
| Lake | Mathlib declares `requiresModuleSystem`, so every non-`module` file importing it warns | all files | `allowNonModules = true` in `lakefile.toml` |
| Performance | one proof (`Wave.mem_operator_powGraph_iff`) needs twice the heartbeat budget to unfold a structurally recursive predicate | 1 | `set_option maxHeartbeats 400000 in`, with a comment |

No theorem statement changed. One hypothesis that Mathlib no longer needs was renamed `_hg`
(`Brezis.theorem_4_29`), and two statements that contain `ContinuousLinearMap.mk (Matrix.mulVecLin A)`
now pass the continuity proof explicitly (`AtkinsonHan` 2.2.8, `lpOpNorm_top`), which by proof
irrelevance is the same proposition.

## 2. Proof-writing patterns that would have avoided the breakage

Each pattern below is backed by sites that broke in this bump.

### 2.1 Qualify lemma names that live in a namespace you merely opened

`open Matrix` plus a bare `mul_apply` silently depended on there being no root `mul_apply`. When
Mathlib added one (and protected the namespaced one), 875 references broke at once. Write the
namespace; it costs seven characters.

```lean
rw [Matrix.mul_apply, Matrix.one_apply]   -- not: rw [mul_apply, one_apply]
```

The same holds inside `namespace Matrix`: a protected name is not reachable by namespace
resolution either. Library code that defines its own `Tensor.sum_apply` etc. should be referred to
as `Tensor.sum_apply` from files that also open `Matrix`.

### 2.2 Do not let a `∀ x ∈ s, p x` stand in for `s ⊆ {x | p x}`

The two used to be the same term; now `{x | p x}` is `Set.ofPred p` and the elaborator does not
unfold membership while the set is still a metavariable. Eta-expand, or go through the API lemma.

```lean
convexHull_min (fun y hy => h y hy) hconv          -- not: convexHull_min h hconv
image_subset_iff.2 fun v hv => mem_preimage.2 (hT v hv)
Nat.sInf_mem (s := {d | P d}) hex                   -- not: Nat.sInf_mem hex  (hex : ∃ d, P d)
```

### 2.3 Give a binder its set when the set is not yet known

`fun x hx => hx.1` where the expected type is `?s ⊆ t` or `MapsTo f ?s t` now fails with "Invalid
projection … `?m.1 x`": the projection is elaborated before `?s` is solved. Annotate the binder, use
the named lemma, or postpone with a tactic block (which runs after the other arguments).

```lean
h.comp continuousOn_fst Set.mapsTo_fst_prod          -- not: … fun p hp => hp.1
indicator_of_notMem (fun (h : x ∈ Ioo a b) ↦ hxb h.2)
inter_eq_left.2 Ioo_subset_Ioi_self                  -- not: inter_eq_left.2 fun x hx ↦ hx.1
closure_minimal (by intro x hx; exact le_of_lt hx.2) hclosed h1
```

The same applies to `show T - t ∈ Ici 0 from sub_nonneg.2 ht`: state membership through
`mem_Ici.2 (…)` rather than relying on `x ∈ Ici a` being `a ≤ x` definitionally, and write binder
types as memberships (`(ht : t ∈ Iic T)`) rather than as the unfolded inequality.

### 2.4 Do not unify set-builder sets against `∩`, `×ˢ`, `⁻¹'`

`refine IsClosed.inter … ?_` against `IsClosed {u | p u ∧ q u}` no longer unifies. Rewrite to the
lattice form first.

```lean
rw [Set.ofPred_and, Set.ofPred_and]
refine IsClosed.inter (isClosed_eq …) ?_
```

### 2.5 After `ext`, rewrite the side that is not a set-builder first

`ext z; rw [Set.mem_ofPred_eq, mem_spectrum_iff]` used to rewrite the right-hand side `z ∈ {z | …}`.
Now `rw` can match `Set.mem_ofPred_eq` against the left-hand side `z ∈ spectrum …` too, by unfolding
a definition that is itself a set-builder, and leaves a `.Mem` term behind. Put the specific `mem_`
lemma first, or `Set.mem_ofPred_eq` last.

```lean
rw [spectrum.mem_iff, Set.mem_ofPred_eq, …]   -- not: rw [Set.mem_ofPred_eq, spectrum.mem_iff, …]
```

### 2.6 Do not rely on `positivity`/`gcongr` seeing through a definition to a hypothesis

`have hκ : 0 < kappa1CC P L p`, then `rw [kappa1CC_def]; gcongr` used to discharge the side goal
`0 ≤ <unfolded kappa1CC>` from `hκ`; now it is left open. Likewise `positivity` with a `set`
abbreviation or a `def` (`hessianMinEig`) that the goal shows unfolded. Close such goals explicitly,
or keep the definition folded.

```lean
gcongr
· exact hκ.le
lt_of_lt_of_le (mul_pos hpd (pow_pos (norm_pos_iff.2 hd) 2)) (minCurvature_mul_norm_sq_le _ d)
```

A type ascription on the `by positivity` block, written with the folded names, also works:
`(by positivity : 0 < (P.ς * κ) ^ (q + 1) / q ! * εm ^ (q + 1))`.

### 2.7 Pass proofs of auto-params in statements

`ContinuousLinearMap.mk (Matrix.mulVecLin A)` relied on the `continuity` auto-param, which stopped
proving it. A statement that depends on a tactic succeeding is fragile; give the proof.

```lean
ContinuousLinearMap.mk (Matrix.mulVecLin A) (Matrix.mulVecLin A).continuous_of_finiteDimensional
```

### 2.8 Prefer named arguments to `@`-applications and positional explicit arguments

`@gramSchmidt_def'' 𝕜 E _ inst₁ inst₂ ι _ _ _ f i` broke because Mathlib dropped one implicit
argument; `natDegree_X_pow_sub_C (n := 2) (r := 1)` broke because the argument was renamed and made
explicit; `Function.ExtendByZero.linearMap K s` broke because an explicit `M` was inserted before
`s`. Prefer letting unification fill implicits, and when an argument must be given, give it by
name only if the name is stable — otherwise state the expected type (`(… : (X ^ 2 - 1).natDegree =
2)`) and let elaboration fill the rest.

### 2.9 Use `convert … using n`

`convert isClosed_univ` now descends through the `Set.ofPred` structure and produces goals of the
form `p x ↔ univ.Mem x`. Bound the depth: `convert isClosed_univ using 1`.

### 2.10 Avoid `rw [...]; rfl` and `try ring` as goal-closers

`rw` now closes some goals by `rfl` itself, turning a trailing `; rfl` into a "no goals" error
(`LinearAlgebra/Subspace.lean`) and a `try ring` into an unused-tactic warning. End the `rw` with
the lemma that finishes the job, or use `simp only [...]`/`exact` for the last step.

## 3. For the next bump

* Get the deprecation and protection lists from the Mathlib diff before building:
  `git -C .lake/packages/mathlib diff OLD NEW -- Mathlib` and grep for `^+protected theorem`,
  `^+@[deprecated`, and signatures where `MeasurableSet` became `NullMeasurableSet`. A scope-aware
  script that qualifies the newly protected names (tracking `namespace`/`section`/`end` with dotted
  names and `open … in`) did 99% of the `Matrix` work here.
* Run `lake build` in the background and fix errors while it runs; downstream modules only show
  their errors on the next pass, so expect several passes.
* `lake env lean` on one file does not pass the `leanOptions` of `lakefile.toml`; add
  `-DmaxSynthPendingDepth=3` or the file will not elaborate as it does under `lake build`.
* Running a standalone `lean` alongside the full build exhausted memory on this machine and made
  unrelated modules fail with "failed to read file … .olean"; rerun before investigating those.

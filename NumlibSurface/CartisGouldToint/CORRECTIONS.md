# Formalized corrections to the supplied textbook transcription

The supplied OCR Markdown contains 232 numbered lemmas, theorems and corollaries.
Forty-five numbered statements and one additional converse are marked incorrect.
The index below records their separate correction companions. The original source
specifications and refutations remain in the TOML plans.

## Corrected companions

The original incorrect specifications and their counterexamples are preserved.
The following companions state the proposed repairs. Their docstrings specify
changed assumptions, algorithms, constants and output conditions. A repaired
companion does not establish its original incorrect statement.

| Source item | Proved companion | Explicit repair |
| --- | --- | --- |
| 1.1.2, converse | [theorem_1_1_2_tangentCone_sufficient](Chapter01/Section01.lean#L234) | Test strict Hessian positivity on nonzero critical directions in the closed tangent cone. |
| 4.1.5 | [theorem_4_1_5_corrected](Chapter04/Section01.lean#L321) | Remove the nonempty improving-direction guard at a stationary point. |
| 5.1.7 | [theorem_5_1_7_corrected](Chapter05/Section01.lean#L444), [theorem_5_1_7_corrected_first_order](Chapter05/Section01.lean#L543), [theorem_5_1_7_corrected_second_order](Chapter05/Section01.lean#L593) | Remove the same blocking guard in every enabled mode. |
| 5.3.6 | [lemma_5_3_6_corrected](Chapter05/Section03.lean#L259) | Normalize the final positive gap by the actual threshold; retain all three regimes. |
| 5.3.9 | [theorem_5_3_9_corrected](Chapter05/Section03.lean#L348) | Conclude convergence of historical minima and objective gaps, rather than arbitrary current measures. |
| 5.4.2 | [lemma_5_4_2_corrected](Chapter05/Section04.lean#L175) | Correct the coercivity coefficient and five-term entry threshold; derive persistent quadratic convergence. |
| 5.4.3 | [lemma_5_4_3_corrected](Chapter05/Section04.lean#L227) | Use the nonnegative natural double-log budget with the missing inner offset. |
| 5.4.4 | [theorem_5_4_4_corrected](Chapter05/Section04.lean#L265) | Derive initialized global/local counts; internal tolerance epsilon/2 ensures the printed strict final inequality. |
| 6.2.1 | [lemma_6_2_1_corrected](Chapter06/Section02.lean#L173) | Impose the missing unit-direction bound. |
| 6.2.2 | [lemma_6_2_2_corrected](Chapter06/Section02.lean#L313) | Retain the true regularizer denominator (p+1)!, in every enabled mode. |
| 6.2.3 | [theorem_6_2_3_corrected](Chapter06/Section02.lean#L356) | Use adaptive-radius Taylor criticality instead of the potentially empty third-derivative-band target; construct actual runs under explicit global smoothness and derivative Lipschitz assumptions. |
| 7.2.1 | [lemma_7_2_1_corrected](Chapter07/Section02.lean#L131) | Close the outer reset guard at residual equality and retain both actual return alternatives. |
| 7.2.7 | [theorem_7_2_7_corrected](Chapter07/Section02.lean#L332) | Close the reset guard, bound the actual objective derivative in the feasible tube, and derive a coarser complete budget from good trials, resets and reflections. |
| 9.3.1 | [theorem_9_3_1_metric](Chapter09/Section03.lean#L141) | Use a nonzero metric least-eigenspace projection; prove convergence and eventual two-sided order for actual inverse solves. |
| 9.3.2 | [theorem_9_3_2_scaled](Chapter09/Section03.lean#L57) | Bound the metric-scaled Hessian, recovering the ordinary bound for the identity metric. |
| 10.2.3 | [corollary_10_2_3_corrected](Chapter10/Section02.lean#L125) | Use a natural ceiling, including the one-step endpoint case. |
| 12.1.5 | [theorem_12_1_5_corrected](Chapter12/Section01.lean#L316) | Replace an isolated Taylor minimum by uniform positive degree-j growth; derive both true and next-Taylor strict minima. |
| 12.2.10 | [lemma_12_2_10_detailed_solver](Chapter12/Section02.lean#L348) | Retain the detailed solver's positive global-gap rule, including its zero-return certificate. |
| 12.2.11 | [lemma_12_2_11_before_certificate](Chapter12/Section02.lean#L529) | Require failure of the next true certificate. |
| 12.2.12 | [lemma_12_2_12_corrected](Chapter12/Section02.lean#L568) | Reduce the common radius coefficient to satisfy the actual obstruction comparison. |
| 12.2.13 | [lemma_12_2_13_corrected](Chapter12/Section02.lean#L824) | Use true candidate failure, including rejected trials; retain both sharp rate branches. |
| 12.2.14 | [theorem_12_2_14_detailed_solver](Chapter12/Section02.lean#L649) | Use genuine detailed model solves and true certificate attainment. |
| 13.1.14 | [lemma_13_1_14_corrected](Chapter13/Section01.lean#L345) | Use the guarded cap max(kappa_s,kappa_h). |
| 13.1.15 | [lemma_13_1_15_corrected](Chapter13/Section01.lean#L724) | Use the genuine cap and finite error budgets for an actual all-passing check. |
| 13.1.16 | [lemma_13_1_16_corrected](Chapter13/Section01.lean#L772) | Derive bounds from the genuine guarded cap before a true certificate. |
| 13.1.17 | [lemma_13_1_17_corrected](Chapter13/Section01.lean#L799) | Use a safe common radius coefficient and the genuine cap. |
| 13.1.18 | [lemma_13_1_18_corrected](Chapter13/Section01.lean#L954) | Use true candidate failure on every trial; retain both sharp rate branches. |
| 13.2.1 | [theorem_13_2_1_uniform_trustRegion](Chapter13/Section02.lean#L22), [theorem_13_2_1_uniform_regularization](Chapter13/Section02.lean#L53) | Bound primitive batch costs uniformly and use the maximum inverse tolerance power. |
| 13.3.5 | [lemma_13_3_5_corrected](Chapter13/Section03.lean#L128) | Use the genuine guarded parameter cap. |
| 13.3.6 | [lemma_13_3_6_corrected](Chapter13/Section03.lean#L307) | Use finite error budgets and the genuine cap to certify actual passing checks. |
| 13.3.7 | [lemma_13_3_7_corrected](Chapter13/Section03.lean#L627) | Require true candidate failure, including rejected trials; retain both sharp model-decrease rates without an extra stopping margin. |
| 14.1.4 | [lemma_14_1_4_detailed_solver](Chapter14/Section01.lean#L229) | Require the positive global-gap detailed model return. |
| 14.1.7 | [lemma_14_1_7_corrected](Chapter14/Section01.lean#L275) | Retain both residual-value errors. |
| 14.1.8 | [lemma_14_1_8_corrected_general](Chapter14/Section01.lean#L559), [lemma_14_1_8_corrected_convex](Chapter14/Section01.lean#L585) | Restore accuracy powers and require next true certificate failure; the first-order branch uses actual unit radii. |
| 14.1.9 | [lemma_14_1_9_corrected_general](Chapter14/Section01.lean#L609), [lemma_14_1_9_corrected_convex](Chapter14/Section01.lean#L633) | Bound decrease of the full composite objective, with next true certificate failure. |
| 14.1.10 | [theorem_14_1_10_detailed_solver](Chapter14/Section01.lean#L327) | Use genuine positive global-gap computations and derive true certificate attainment with initialized counts. |
| 14.2.2 | [lemma_14_2_2_ARqp_before_certificate](Chapter14/Section02.lean#L271) | Restrict to the exact detailed ARqp algorithm, global derivative Lipschitz assumptions and next true certificate failure; retain adaptive higher-order radii. |
| 14.2.4 | [theorem_14_2_4_ARqp_detailed](Chapter14/Section02.lean#L318) | Restrict to the exact detailed ARqp algorithm with explicit global regularity; construct actual runs, all-order certificates, quantitative radii and initialized counts. |
| 14.3.1 | [theorem_14_3_1_corrected](Chapter14/Section03.lean#L408) | Require formal equality jets to lift to actual feasible curves; derive ordered composition derivatives at a constrained minimum. |
| 14.3.3 | [theorem_14_3_3_corrected](Chapter14/Section03.lean#L93) | Take the natural ceiling of the real logarithmic bound. |
| 14.3.4 | [theorem_14_3_4_corrected](Chapter14/Section03.lean#L154) | Bound the sum of per-call maxima by a valid uniform geometric coefficient. |
| 14.3.5 | [lemma_14_3_5_corrected](Chapter14/Section03.lean#L469) | Complete inner calls at absolute tolerances and close resets. Classify the actual returned point, retaining higher-order increment errors, exact first-order bounds and common-kernel certificates through order three. |
| 14.3.9 | [theorem_14_3_9_corrected](Chapter14/Section03.lean#L490) | Complete both phases with genuine constrained solves under explicit stronger global regularity; construct actual stopping executions and prove a coarser phase-one plus outer-times-inner budget, with the corrected guarded output. |
| B.2.1 | [lemma_B_2_1_corrected](AppendixB/Chapter02.lean#L62) | Bound the initial endpoint jets as well as residuals. |
| B.2.6 | [lemma_B_2_6_first_local](AppendixB/Chapter02.lean#L220) | Retain the canonical construction and prove the first local ray minimum at every preterminal iterate. |
| B.4.1 | [lemma_B_4_1_corrected](AppendixB/Chapter04.lean#L49) | Replace false exact norm constants by uniform homogeneous bounds; retain the exact radial formula and valid-order convexity. |

Additional sharper or more general alternatives are documented beside these
companions. In particular, literal EDA stopping guarantees with an effective
margin and unconditional coarser current-check bounds are distinct from the
sharp true-candidate model-decrease correction.

The two exact-ARqp replacements in Section 14.2 intentionally restrict the
algorithm class. They make no claim for the other five printed variants.
The ten other deferred numbered statements are listed in the book index
[documentation](../CartisGouldToint.lean); this correction index does not mark
those original statements as proved.

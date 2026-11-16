/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter15.Section01
import NumlibSurface.ConnGouldToint.Chapter15.Section02
import NumlibSurface.ConnGouldToint.Chapter15.Section03
import NumlibSurface.ConnGouldToint.Chapter15.Section04
import NumlibSurface.ConnGouldToint.Chapter15.RelaxedSQP
import NumlibSurface.ConnGouldToint.Chapter15.SQPVariants
import NumlibSurface.ConnGouldToint.Chapter15.Section05
import NumlibSurface.ConnGouldToint.Chapter15.FilterAlgorithm
import NumlibSurface.ConnGouldToint.Chapter15.Corrections
import NumlibSurface.ConnGouldToint.Chapter15.ByrdOmojokun
import NumlibSurface.ConnGouldToint.Chapter15.TrialSegmentCounterexample

/-!
# Conn, Gould and Toint, Chapter 15: Sequential Quadratic Programming Methods

Chapter 15 of [conn2000trust] treats sequential quadratic programming (SQP) methods for nonlinear
programs. The modules cover the programs (Section 15.1), local convergence (Section 15.2),
globalization by an exact penalty function (Section 15.3), composite-step trust-region SQP methods
with relaxed linearizations, second-order corrections and the Byrd–Omojokun method (Section 15.4),
and filter methods (Section 15.5).

## Contents

| Source | Module | Subject |
|---|---|---|
| §15.1 The nonlinear programs of SQP | `Chapter15.Section01` | (15.1.1)–(15.1.2) |
| §15.2 Local convergence of SQP | `Chapter15.Section02` | Theorems 15.2.1–15.2.2 |
| §15.3 SQP with an exact penalty | `Chapter15.Section03` | Theorem 15.3.1 to Theorem 15.3.7 |
| §15.4 Relaxed linearization SQP | `Chapter15.Section04` | Lemma 15.4.1 to Lemma 15.4.21 |
| §15.4 Relaxed SQP algorithms | `Chapter15.RelaxedSQP` | Algorithms 15.4.1–15.4.4 |
| §15.4 Trial segments | `Chapter15.TrialSegmentCounterexample` | counterexample for Lemma 15.4.3 |
| §15.4 Corrections | `Chapter15.Corrections` | Lemmas 15.4.13–15.4.14, Theorem 15.4.15 |
| §15.4 SQP variants | `Chapter15.SQPVariants` | Algorithms 15.4.5–15.4.8 |
| §15.4 Byrd–Omojokun SQP convergence | `Chapter15.ByrdOmojokun` | Theorems 15.4.22–15.4.25 |
| §15.5 Filter SQP methods | `Chapter15.Section05` | Lemma 15.5.1 to Theorem 15.5.14 |
| §15.5 The filter SQP algorithms | `Chapter15.FilterAlgorithm` | Algorithms 15.5.1–15.5.2 |
-/

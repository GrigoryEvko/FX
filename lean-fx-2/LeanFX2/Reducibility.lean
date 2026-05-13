import LeanFX2.Reducibility.Basic
import LeanFX2.Reducibility.Neutral
import LeanFX2.Reducibility.Predicate
import LeanFX2.Reducibility.Classifier
import LeanFX2.Reducibility.Foundation
import LeanFX2.Reducibility.StableBase
import LeanFX2.Reducibility.NeutralSNFoundation
import LeanFX2.Reducibility.NeutralSNHott
import LeanFX2.Reducibility.NeutralSNIntro
import LeanFX2.Reducibility.NeutralSNClosure
import LeanFX2.Reducibility.TypedCR2Direct
import LeanFX2.Reducibility.TypedCR2Generic
import LeanFX2.Reducibility.TypedCR2Compound
import LeanFX2.Reducibility.TypedCR2Wrapup
import LeanFX2.Reducibility.FundamentalWrappers
import LeanFX2.Reducibility.FundamentalEliminators
import LeanFX2.Reducibility.FundamentalAliases
import LeanFX2.Reducibility.FundamentalCubical

/-! # LeanFX2.Reducibility — Tait reducibility candidates (shim)

The historical 20k-line monolith carved into 18 sub-modules along
the natural Tait-cascade dependency DAG.  This file is a pure
shim that re-exports every sub-module so existing consumers of
`import LeanFX2.Reducibility` see the full predicate suite without
modification.

## Module map

The split follows the Tait reducibility pipeline phase-by-phase:

| Module                          | Phase                                    |
| ------------------------------- | ---------------------------------------- |
| `Reducibility.Basic`            | SN foundation (Reducible-independent)    |
| `Reducibility.Neutral`          | IsNeutral + neutrality preservation      |
| `Reducibility.Predicate`        | `def Reducible` by recursion on Ty       |
| `Reducibility.Classifier`       | SN-direct arms + IsSNDirect              |
| `Reducibility.Foundation`       | ReducibleSubst + Renaming-stable + raw   |
| `Reducibility.StableBase`       | K12.20.U4 stable fundamental base        |
| `Reducibility.NeutralSN*`       | K12.20.C neutral & natSucc SN cascade    |
| `Reducibility.TypedCR2*`        | K12.20.D-U typed forward-step closure    |
| `Reducibility.Fundamental*`     | K12.20.U4/K12.21-K12.27 fundamental cases|

Each sub-module imports only its predecessors in the dependency
DAG — `lake -j` parallelizes across the chain.

## Architectural history

K12.1+K12.2 originally shipped `Reducible` as an `inductive Prop`
with a `Reducible.nat` SN closure arm.  K12.3+K12.4 added five
more closed-leaf arms (bool / unit / empty / interval / universe)
identical in shape.

K12.5 attempted to extend with the standard Tait function-type
closure but Lean 4 v4.29.1 rejected the constructor's
left-of-arrow hypothesis as non-positive.  Canonical mathlib
pattern: pivot from `inductive` to `def`-by-recursion on Ty
(Reducible.Predicate).  This works because recursive references
descend on a structurally-smaller Ty (`domainType` and
`codomainType` are proper sub-terms of `Ty.arrow ...`).

## What ships

* `Reducible` — def by recursion on 25 Ty ctors, K12.1–K12.16
* `Reducible.IsSNDirect` — predicate classifying SN-direct arms
* `ReducibleSubst` — substitution-reducibility carrier
* `IsRenamingStableReducible` / `IsRenamingStableReducibleSubst` —
  K12.20.U3 renaming-stability scaffolding for the Lam case
* All compound CR2 / CR3 lift theorems (K12.20.D-T)
* Fundamental-theorem cases K12.19 through K12.27

## Root status

Layer 3 metatheory (top-level `LeanFX2.Reducibility` module).
Provides foundation for the Tait SN theorem (M04 / K12.27). -/

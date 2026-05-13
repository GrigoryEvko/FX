import LeanFX2.Algo.WHNF.Evaluator
import LeanFX2.Algo.WHNF.NullaryInversions
import LeanFX2.Algo.WHNF.PayloadInversions

/-! # LeanFX2.Algo.WHNF — weak head normal form classifier (shim)

This module is now a re-exporting shim.  All content lives in the
following sub-modules, carved from the original 1337-line file during
the v2.0 mega-refactor so each piece stays under ~700 LoC and parallel
elaboration can carry per-file work independently.

| Sub-module                | LoC | Family                                       |
|---------------------------|-----|----------------------------------------------|
| `WHNF.Evaluator`          | 384 | `Term.HeadCtor` enum, `Term.headCtor`, `Term.isWHNF` |
| `WHNF.NullaryInversions`  | 446 | raw recovery for nullary heads (boolTrue/False, natZero, listNil, optionNone) |
| `WHNF.PayloadInversions`  | 533 | raw recovery for payload heads (natSucc, listCons, optionSome, eitherInl, eitherInr) + `unit` |

## What `Term.isWHNF` decides

`Term.isWHNF` returns `true` iff a typed term is in **weak head normal
form** — that is, the head constructor is a value-form (lam, pair,
refl, ...) or a neutral form (variable, application of variable, or
elimination of a neutral) rather than a redex.  See
`WHNF.Evaluator` for the full classification table.

## Why classify

`Algo/DecConv` decides convertibility by reducing both sides to WHNF
and structurally comparing.  WHNF is finer than full normal form
(strictly weaker reduction), but enough for decidable conversion
because Church-Rosser ensures common reducts share WHNF heads.

## Implementation discipline

To avoid propext leaks (wildcards on dep-indexed matches always leak),
we project Term ctor identity to a flat enum `Term.HeadCtor` via full
enumeration first, then use Bool dispatch on the flat enum.  The
result: `Term.isWHNF` is zero-axiom.

## Root status

Layer 3 algorithm aggregator.  Zero-axiom under `LeanFX2Audit`. -/

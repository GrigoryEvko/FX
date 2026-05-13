import LeanFX2.Reduction.ParRed.ParInductive
import LeanFX2.Reduction.ParRed.ParStepLift
import LeanFX2.Reduction.ParRed.ParCasts

/-! # LeanFX2.Reduction.ParRed — typed parallel reduction (shim)

`Step.par source target : Prop` reduces all subterms simultaneously,
including any contracted redex.  Reflexive (zero parallel-steps =
identity) and the standard vehicle for proving confluence: the
diamond property holds for `Step.par`, and `Step.par`'s transitive
closure equals `StepStar`'s.

## Two-Ty + two-RawTerm signature

Mirrors `Step` / `StepStar`: source/target Ty + raw indices are
free.  This handles dep-position cong rules (`pair`, `appPi`,
`snd`, etc.) where parallel reduction in one position changes the
required type of another.

## η deliberately omitted

Stays in opt-in `Reduction/Eta.lean` (when added).  βι confluence
proof should not carry η weight per architectural commitment.

## Carved into three sub-modules

The original file split along the natural semantic axis of
declaration kind: one monolithic inductive, one tactic-mode lift
theorem, and a family of propositional-transport helpers.

| Sub-module | Content |
| --- | --- |
| `ParRed.ParInductive` | The `Step.par` inductive (atomic — cannot be split) |
| `ParRed.ParStepLift` | `Step.toPar` single-step ⇒ parallel lift |
| `ParRed.ParCasts` | Six propositional-transport cast helpers |

## Root status

Zero-axiom — every shipped declaration in the three sub-modules is
a `theorem`/`def`/`inductive` with a body. -/

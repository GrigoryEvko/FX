import LeanFX.Mode.Defn
import LeanFX.Syntax.Term

/-! # LeanFX — ground-up formalisation of FX in Lean 4.

This is the public root of the package.  Every public-facing
definition lives in `LeanFX/...` and is re-exported here in
dependency order.

## One kernel, one file

A single intrinsic kernel that **bypasses Lean 4's mutual-index
limitation by sequential composition** — declare `RawTerm : Nat →
Type` BEFORE `Ty`, so `Ty.id`'s reference to `RawTerm` is a
forward citation, not a mutual cross-reference.

Everything lives in `LeanFX.Syntax.Term`:

  * `RawTerm : Nat → Type` — well-scoped raw syntax (25
    constructors including `refl` and `idJ`).  Substrate for
    identity-type endpoints.

  * `Ty : Nat → Nat → Type` — well-scoped intrinsic types,
    indexed by universe level + scope.  `Ty.id carrier lhs rhs`
    references RawTerm endpoints in argument position.

  * `Ctx : Mode → Nat → Nat → Type` — typed contexts.

  * `Term : Ctx → Ty → Type` — intrinsically-typed terms.
    Constructor signatures *are* the typing rules.  Includes
    `Term.refl` and `Term.idJ` for identity-type introduction
    and elimination.

  * `Term.toRaw : Term Γ T → RawTerm scope` — the bridge that
    erases intrinsic typing back to raw syntax.

  * Substitution, parallel reduction (`Step`, `Step.par`,
    `StepStar`, `Conv`), and the J ι-rule.

~9,400 lines, 100% zero-axiom across every declaration.

## The unified architecture

Earlier prototypes split this into two files: an intrinsic kernel
(this `Term.lean`) and a raw mutual kernel (`Raw.lean`) that
hosted `Ty.tyId` mutual with raw `Term`.  The mutual approach
was needed because `Ty` had to reference Term-shaped values, and
intrinsic mutual `Ctx⇄Ty⇄Term` is rejected by Lean 4's elaborator
(`feedback_lean_mutual_index_rule.md`).

The sequential-composition trick (RawTerm declared before Ty)
sidesteps the elaborator restriction entirely while keeping
intrinsic discipline.  `Raw.lean` was deleted in v2.2p.

## Trust base

  * Lean 4 kernel (~6 KLoC C++; accepted as TCB).
  * `LeanFX.Mode.Defn` — the four-mode enum.  Audited as input data.
  * `LeanFX.Syntax.Term` — RawTerm + Ty + Ctx + Term + reductions.

Everything else — typing, conversion, subject reduction, the
bidirectional checker, the elaborator — operates *on* the kernel
and physically cannot extend it. -/

import LeanFX.Mode.Modality
import LeanFX.Mode.TwoCell
import LeanFX.Mode.Composable
import LeanFX.Mode.Collision
import LeanFX.Syntax.Inductive
import LeanFX.Syntax.Code
import LeanFX.Syntax.Term
import LeanFX.Syntax.DependentJ
import LeanFX.Frontend.Token
import LeanFX.Frontend.Surface
import LeanFX.Tools.AuditAll

/-! # LeanFX — ground-up formalisation of FX in Lean 4.

This is the public root of the package.  Every public-facing
definition lives in `LeanFX/...` and is re-exported here in
dependency order.

## Kernel module spine

The intrinsic kernel is split by dependency layer while preserving
`LeanFX.Syntax.Term` as the stable public import:

  * `LeanFX.Syntax.RawTerm` — well-scoped raw syntax.
  * `LeanFX.Syntax.Ty` — intrinsic types and renaming.
  * `LeanFX.Syntax.RawSubst` — raw substitution and categorical laws.
  * `LeanFX.Syntax.Subst` — joint type/raw substitution.
  * `LeanFX.Syntax.Context` — contexts and `varType`.
  * `LeanFX.Syntax.TypedTerm` — intrinsically-typed terms and renaming.
  * `LeanFX.Syntax.TermSubst` — term substitution and HEq functoriality.
  * `LeanFX.Syntax.ToRaw` — intrinsic-to-raw erasure bridge.
  * `LeanFX.Syntax.Reduction` — `Step`, `StepStar`, `Step.par`, `Conv`.
  * `LeanFX.Syntax.Identity` — external `IdProof` helpers.
  * `LeanFX.Syntax.Smoke` — constructor/reduction smoke coverage.
  * `LeanFX.Mode.Modality` — abstract mode 1-category substrate.
  * `LeanFX.Mode.TwoCell` — abstract Prop-valued modal 2-cells.
  * `LeanFX.Mode.Composable` — decidable admissible modal composition.
  * `LeanFX.Mode.Collision` — concrete finite FX collision catalog.
  * `LeanFX.Syntax.Inductive` — generic inductive-family specs.
  * `LeanFX.Syntax.Code` — Tarski-code substrate, imported explicitly
    because it is not part of the stable `Syntax.Term` kernel spine.
  * `LeanFX.Syntax.DependentJ` — dependent-J motive signature shape,
    imported explicitly because it is not yet a kernel constructor.
  * `LeanFX.Tools.AuditAll` — build-time zero-axiom regression gate.

The split is still one sequential kernel architecture: `RawTerm` is
declared before `Ty`, so `Ty.id` references raw endpoints without a
mutual `Ty`/`Term` block.  The stable term kernel remains available
through `import LeanFX.Syntax.Term`; future-facing substrates such as
`Code`, `Inductive`, and `DependentJ` are imported explicitly at the
package root until they have kernel consumers.

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
  * `LeanFX.Syntax.*` — RawTerm + Ty + Ctx + Term + reductions.

Everything else — typing, conversion, subject reduction, the
bidirectional checker, the elaborator — operates *on* the kernel
and physically cannot extend it. -/

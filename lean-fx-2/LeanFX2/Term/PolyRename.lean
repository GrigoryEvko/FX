import LeanFX2.Term.Rename
import LeanFX2.Term.ToPoly
import LeanFX2.Term.PolyToTerm
import LeanFX2.Foundation.Polygraph.PolyTerm
import LeanFX2.Foundation.Polygraph.PolyTermAction
import LeanFX2.Foundation.Polygraph.PolyTermRoundtrip

/-! # `PolyTerm.rename` — typed renaming on the polygraph mirror.

K11.13 Phase C-2 (#1745): lifts the typed `Term.rename` machinery
from `LeanFX2/Term/Rename.lean` to operate on `PolyTerm` via the
typed forward + backward bijection (K11.10-B + K11.11).

## Composition definition

Direct case-by-case PolyTerm.rename would be a 77-case structural
recursion mirroring `Term.rename` with 8 raw-in-Ty cast points
(appPi / pair / snd / boolElim / refl / oeqRefl / idStrictRefl /
funextRefl) needing both `Ty.subst0_rename_commute` and Phase C-1's
`RawPolyTerm.toRawTerm_rename_commute` at each cast.  ~600 LoC.

The composition definition is far cleaner:

  1. `polyTerm.toTerm` (K11.11) — convert to `Term` at index
     `rawPoly.toRawTerm`.
  2. `Term.rename termRenaming` — rename in the typed Term layer
     (existing 77-case Term.rename infrastructure).
  3. `.toPoly` (K11.10-B) — convert back to `PolyTerm` at index
     `(rawPoly.toRawTerm.rename rho).toRawPoly`.
  4. Cast through the raw-level equation
     `(rawPoly.toRawTerm.rename rho).toRawPoly = rawPoly.rename rho`,
     which factors as Phase A's `RawTerm.rename_toRawPoly_commute`
     applied at `rawTerm = rawPoly.toRawTerm`, then K11.12's
     `RawPolyTerm.toRawTerm_toRawPoly` collapsing the roundtrip.

The composition is propositionally equal to a direct case-by-case
PolyTerm.rename (Phase C-3 will ship the typed
`Term.rename_toPoly_commute` headline that proves this).

## Audit

Both `PolyTerm.rename` and the `PolyTerm.weaken` corollary ship
zero-axiom — every ingredient (K11.10-B, K11.11, K11.12 forward
roundtrip, Phase A commute) is itself zero-axiom, and the cast is a
propext-clean `▸` over `PolyTerm`'s third index. -/

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Typed renaming on `PolyTerm`.  Defined via the K11.10-B /
K11.11 typed bijection: route `polyTerm` through `Term`, rename
via the existing `Term.rename` infrastructure, route back via
`Term.toPoly`, and cast the resulting raw-payload index from
`(rawPoly.toRawTerm.rename rho).toRawPoly` to `rawPoly.rename rho`
using Phase A's commute + K11.12's roundtrip. -/
def PolyTerm.rename {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {someType : Ty level sourceScope}
    {rawPoly : RawPolyTerm sourceScope}
    (polyTerm : PolyTerm sourceCtx someType rawPoly) :
    PolyTerm targetCtx (someType.rename rho) (rawPoly.rename rho) :=
  let renamedTerm : Term targetCtx (someType.rename rho)
                          (rawPoly.toRawTerm.rename rho) :=
    Term.rename termRenaming polyTerm.toTerm
  let resultPolyAtCommutedIndex :
      PolyTerm targetCtx (someType.rename rho)
          (rawPoly.toRawTerm.rename rho).toRawPoly :=
    renamedTerm.toPoly
  let rawPolyIndexEq :
      (rawPoly.toRawTerm.rename rho).toRawPoly = rawPoly.rename rho := by
    rw [RawTerm.rename_toRawPoly_commute rawPoly.toRawTerm rho,
        RawPolyTerm.toRawTerm_toRawPoly rawPoly]
  rawPolyIndexEq ▸ resultPolyAtCommutedIndex

/-- Single-binder weakening on a typed `PolyTerm`: lift through one
new binding via the canonical weakening `TermRenaming`.  The result
sits in the extended context at the weakened Ty + RawPolyTerm.weaken
of the raw payload (definitionally — `RawPolyTerm.weaken` is
`@[reducible]` and unfolds to `rename RawRenaming.weaken`). -/
@[reducible] def PolyTerm.weaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {someType : Ty level scope}
    {rawPoly : RawPolyTerm scope} (newType : Ty level scope)
    (polyTerm : PolyTerm context someType rawPoly) :
    PolyTerm (context.cons newType) someType.weaken rawPoly.weaken :=
  PolyTerm.rename (TermRenaming.weakenStep context newType) polyTerm

end LeanFX2

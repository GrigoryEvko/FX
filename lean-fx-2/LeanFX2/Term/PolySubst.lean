import LeanFX2.Term
import LeanFX2.Term.Subst
import LeanFX2.Term.ToPoly
import LeanFX2.Term.PolyToTerm
import LeanFX2.Foundation.Polygraph.PolyTerm
import LeanFX2.Foundation.Polygraph.PolyTermAction
import LeanFX2.Foundation.Polygraph.PolyTermRoundtrip

/-! # `PolyTerm.subst` — typed substitution on the polygraph mirror.

K11.13 Phase D (#1745): lifts the typed `Term.subst` machinery from
`LeanFX2/Term/Subst.lean` to operate on `PolyTerm` via the typed
forward + backward bijection (K11.10-B + K11.11).  Mirrors Phase C-2's
composition pattern for `PolyTerm.rename`.

## Composition definition

Direct case-by-case PolyTerm.subst would be a 77-case structural
recursion mirroring `Term.subst` with 11 raw-in-Ty cast points needing
both `Ty.subst0_subst_commute` and Phase B's
`RawPolyTerm.toRawTerm_subst_commute` at each cast.  ~600 LoC.

The composition definition is far cleaner:

  1. `polyTerm.toTerm` (K11.11) — convert to `Term` at index
     `rawPoly.toRawTerm`.
  2. `Term.subst termSubst` — substitute in the typed Term layer
     (existing 77-case `Term.subst` infrastructure).
  3. `.toPoly` (K11.10-B) — convert back to `PolyTerm` at index
     `(rawPoly.toRawTerm.subst sigma.forRaw).toRawPoly`.
  4. Cast through the raw-level equation
     `(rawPoly.toRawTerm.subst sigma.forRaw).toRawPoly =
        rawPoly.subst sigma.forRaw.toRawPolySubst`,
     which factors as Phase B's `RawTerm.subst_toRawPoly_commute`
     applied at `rawTerm = rawPoly.toRawTerm`, then K11.12's
     `RawPolyTerm.toRawTerm_toRawPoly` collapsing the roundtrip.

## Audit

Both `PolyTerm.subst` and the `PolyTerm.subst0` corollary ship
zero-axiom — every ingredient (K11.10-B, K11.11, K11.12 forward
roundtrip, Phase B commute) is itself zero-axiom, and the cast is a
propext-clean `▸` over `PolyTerm`'s third index. -/

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Typed substitution on `PolyTerm`.  Defined via the K11.10-B /
K11.11 typed bijection: route `polyTerm` through `Term`, substitute
via the existing `Term.subst` infrastructure, route back via
`Term.toPoly`, and cast the resulting raw-payload index from
`(rawPoly.toRawTerm.subst sigma.forRaw).toRawPoly` to
`rawPoly.subst sigma.forRaw.toRawPolySubst` using Phase B's commute +
K11.12's roundtrip. -/
def PolyTerm.subst {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {someType : Ty level sourceScope}
    {rawPoly : RawPolyTerm sourceScope}
    (polyTerm : PolyTerm sourceCtx someType rawPoly) :
    PolyTerm targetCtx (someType.subst sigma)
        (rawPoly.subst sigma.forRaw.toRawPolySubst) :=
  let substitutedTerm : Term targetCtx (someType.subst sigma)
                          (rawPoly.toRawTerm.subst sigma.forRaw) :=
    Term.subst termSubst polyTerm.toTerm
  let resultPolyAtCommutedIndex :
      PolyTerm targetCtx (someType.subst sigma)
          (rawPoly.toRawTerm.subst sigma.forRaw).toRawPoly :=
    substitutedTerm.toPoly
  let rawPolyIndexEq :
      (rawPoly.toRawTerm.subst sigma.forRaw).toRawPoly =
        rawPoly.subst sigma.forRaw.toRawPolySubst := by
    rw [RawTerm.subst_toRawPoly_commute rawPoly.toRawTerm sigma.forRaw,
        RawPolyTerm.toRawTerm_toRawPoly rawPoly]
  rawPolyIndexEq ▸ resultPolyAtCommutedIndex

/-- Singleton substitution on a typed `PolyTerm` for β-reduction:
substitute the most recent binding (Fin position 0) with `argumentTerm`,
shifting the rest down.  Result sits in the context shrunk by one
binding at the substituted Ty + `RawPolyTerm.subst` with
`RawPolyTermSubst.singleton` on the raw payload. -/
@[reducible] def PolyTerm.subst0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {argumentType : Ty level scope}
    {argumentRaw : RawTerm scope}
    {bodyType : Ty level (scope + 1)}
    {bodyRawPoly : RawPolyTerm (scope + 1)}
    (argumentTerm : Term context argumentType argumentRaw)
    (bodyPoly : PolyTerm (context.cons argumentType) bodyType bodyRawPoly) :
    PolyTerm context (bodyType.subst0 argumentType argumentRaw)
        (bodyRawPoly.subst
          (RawTermSubst.singleton argumentRaw).toRawPolySubst) :=
  PolyTerm.subst (TermSubst.singleton argumentTerm) bodyPoly

end LeanFX2

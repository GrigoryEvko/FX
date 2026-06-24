import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Core.Rewriting.Conversion.ConvCongruence
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename

/-! # IntroOutputTypeCongruence — the introducer output-type congruence ingredient of the GENERAL union SR

The companion of `ElimOutputTypeCongruence` for the `intro` arm.  The native single-step union subject
reduction at an ARBITRARY classifier (the general `congruenceClosesAux`, the right vehicle for the
eliminator-congruence gate of #1697 since it threads the per-premise IH inline) re-types a `.mkGen` cell when
one child steps, then re-classifies at the `Conv`-equal output type.  For the `intro` arm that output-type
congruence is needed only for the TWO introducer rows whose output reads a STEPPING child:

  * **lam** — output `piTyCodeCell domainCode codomainCode` (`argShifts [0, 1]`, `paramShifts [1]`): the
    `domainCode` is the FIRST child (shift 0); a domain-annotation step drifts the output, discharged by
    `Conv.ofChildren` congruence in the domain position (the body child does not occur in the output, so a
    body step is `Conv.refl`).
  * **pathLam** — output `bridgeTypeCell carrierCode (subst0 body intervalZeroCell) (subst0 body
    intervalOneCell)` (`argShifts [1]`, `paramShifts [0]`): the `body` is the sole child and occurs in BOTH
    bridge endpoints under `subst0`; a body step drifts both endpoints, discharged by `subst0` body-leg
    congruence (`Conv.subst0` with a `Conv.fromStep` on the body and `Conv.refl` on the interval point) inside
    a three-child `Conv.ofChildren` (the carrier param is `Conv.refl`).

Every OTHER introducer row (`boolTrue`/`boolFalse`/`unit`/`interval0`/`interval1`/`natZero`/`natSucc`/
`listCons`/`optionSome`/`optionNone`/`listNil`/`eitherInl`/`eitherInr`/`pair`/`refl`) has an output type that
reads only the type-index PARAMS (or a fixed data code), never a stepping child, so its output-type
Conv-stability is `Conv.refl` — nothing to prove.  So `lam` and `pathLam` are the ENTIRE non-trivial content
of the introducer-arm output-type congruence, completing the output-Conv ingredient across BOTH the
eliminator and introducer arms of the general union SR.

(At the EMPTY type the `intro` arm of the consistency-facing closer REFUTES rather than re-types — an
introducer's data/Pi/bridge-code classifier is never `Conv emptyTypeCell` — so these lemmas are not consumed
by the empty-type closer; they are the introducer half of the GENERAL closer.)

## Zero-axiom

A composition of the shipped `Conv.ofChildren` / `ConvChildren.consC` / `Conv.subst0` / `Conv.fromStep` /
`Conv.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration audit-gated in `FX1PolyAudit`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ The `lam` introducer's output type is `Conv`-stable when its DOMAIN-annotation child steps.**  `lam`'s
output is `piTyCodeCell domainCode codomainCode = .mkGen gen_piTyCode () [domainCode, codomainCode]`; the
`domainCode` is the first (shift-0) child, so a domain step drifts the output.  Discharged by `Conv.ofChildren`
congruence in the domain position with `Conv.refl` on the codomain.  (A body-child step leaves the output
unchanged — the body is not read by the output type — so it is `Conv.refl`, no lemma needed.) -/
theorem lamIntroOutputType_isConvStableUnderDomainStep {scope : Nat}
    (codomainCode : RawTerm (scope + 1)) {domainCode updatedDomainCode : RawTerm scope}
    (domainStep : Step domainCode updatedDomainCode) :
    Conv (piTyCodeCell domainCode codomainCode) (piTyCodeCell updatedDomainCode codomainCode) :=
  Conv.ofChildren
    (ConvChildren.consC (Conv.fromStep domainStep)
      (ConvChildren.consC (Conv.refl codomainCode) ConvChildren.nilC))

/-- **★ The `pathLam` introducer's output type is `Conv`-stable when its BODY child steps.**  `pathLam`'s
output is `bridgeTypeCell carrierCode (subst0 body intervalZeroCell) (subst0 body intervalOneCell)`; the sole
child `body` occurs in BOTH endpoints under `subst0`, so a body step drifts both.  Discharged by a three-child
`Conv.ofChildren`: `Conv.refl` on the carrier param, and `Conv.subst0` body-leg congruence (`Conv.fromStep`
on the body, `Conv.refl` on the interval point) on each endpoint. -/
theorem pathLamIntroOutputType_isConvStableUnderBodyStep {scope : Nat}
    (carrierCode : RawTerm scope) {body updatedBody : RawTerm (scope + 1)}
    (bodyStep : Step body updatedBody) :
    Conv
      (bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
        (RawTerm.subst0 body intervalOneCell))
      (bridgeTypeCell carrierCode (RawTerm.subst0 updatedBody intervalZeroCell)
        (RawTerm.subst0 updatedBody intervalOneCell)) :=
  Conv.ofChildren
    (ConvChildren.consC (Conv.refl carrierCode)
      (ConvChildren.consC (Conv.subst0 (Conv.fromStep bodyStep) (Conv.refl intervalZeroCell))
        (ConvChildren.consC (Conv.subst0 (Conv.fromStep bodyStep) (Conv.refl intervalOneCell))
          ConvChildren.nilC)))

end FX1Poly.Typed

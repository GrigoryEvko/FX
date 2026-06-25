import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionPathAppInversion — PATH-ELIMINATION (pathApp) inversion for the
    UNION (TYTAB-2 SRINV: the OUTER inversion unconditional endpoint-β subject reduction needs)

For a `pathAppCell path argument` SUBJECT typed in the native union `HasTypeUnion`, this recovers the path
elimination premises: the path is union-typed at a bridge code `bridgeTypeCell carrierCode left right`, the
argument (interval endpoint) at `intervalTypeCell`, and the classifier is convertible to the constant carrier
`carrierCode` (the pathApp output type).  The path twin of `HasTypeUnion.invertAtAppHead` — the keystone
inversion the W5 bundle SR theorem deferred for the endpoint-β (`gen_pathApp`) row.

## The recipe (the dual of `invertAtAppHead`, with the ofGrown disjunct REFUTED)

`induction derivation` with `subjectShape : subject = pathAppCell path argument` reverted:

  * `var` / `universeFormation` — head clash (`gen_pathApp` vs `gen_var` / `gen_universeCode`).
  * `conv` — recurse on the typed premise (same subject), re-thread the classifier `Conv`.
  * `ofGrown` — the grown engine types NO `pathApp` cell (`pathApp` is a data eliminator, not one of the six
    host roots); `HasTypeDescPi.pathAppCellHasNoTyping` refutes the disjunct.  (Contrast `invertAtAppHead`,
    whose `ofGrown` routes THROUGH the host because `app` IS a host root.)
  * `formationRule` / `intro` — `formationRuleOf gen_pathApp = none` / `introRuleOf gen_pathApp = none` refute
    after the head pin.
  * `elim` — the `gen_pathApp` row is the SURVIVOR: `elimMemberCellRootGenerator` pins the generator,
    `elimRuleOf_pathApp` pins the row to `pathAppElimRule`, then destructure the `[0,0]` args / `[0,0,0]`
    params and read the two obligations (path at the bridge code, argument at the interval) off
    `premisesHold`; the classifier IS the output carrier, so `Conv.refl`.

## Zero-axiom

Reverted-`subjectShape` induction over the seven union arms + `elimMemberCellRootGenerator` /
`introMemberCellRootGenerator` head pins + `pathAppCellHasNoTyping` for the host refutation + the
unconditional `Conv.trans` / `Conv.sym` / `Conv.refl` + `childCons` injection drilling.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **★ Path-elimination (pathApp) inversion for the union.**  A union typing of a `pathAppCell path
argument`-headed subject has the path union-typed at a bridge code, the argument union-typed at the interval
type, and the classifier convertible to the constant carrier.  The union dual of `invertAtAppHead` for the
path eliminator — the OUTER inversion the unconditional endpoint-β SR consumes (with `invertAtPathLamHead`
for the path abstraction). -/
theorem HasTypeUnion.invertAtPathAppHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {path argument : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = pathAppCell path argument) :
    ∃ (carrierCode leftEndpoint rightEndpoint : RawTerm scope),
      HasTypeUnion profile context path
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context argument intervalTypeCell ∧
      Conv classifier carrierCode := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `pathApp` row (args `[path, argument]`, params
  -- `[carrierCode, leftEndpoint, rightEndpoint]`; obligation order `[path, argument]`; `outputType =
  -- carrierCode`).  The conclusion's `Conv` runs classifier→carrier, so the row's output `Conv` is `.sym`med.
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := pathAppElimRule)
      (show elimRuleOf Generator.gen_pathApp = some pathAppElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _pathChild (.childCons _argumentChild .childNil),
    .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨carrierCode, leftEndpoint, rightEndpoint,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      outputConv.sym⟩

end FX1Poly.Typed

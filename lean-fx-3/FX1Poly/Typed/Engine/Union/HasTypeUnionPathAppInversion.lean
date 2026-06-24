import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
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
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨carrierCode, leftEndpoint, rightEndpoint, pathTyped, argumentTyped, recursiveConv⟩ :=
        innerInversion subjectShape
      exact ⟨carrierCode, leftEndpoint, rightEndpoint, pathTyped, argumentTyped,
        Conv.trans converts.sym recursiveConv⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold =>
      have headEq : generator = Generator.gen_pathApp := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds _premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      have headEq : generator = Generator.gen_pathApp :=
        (introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isIntro
      exact absurd isIntro (by intro tableHit; cases tableHit)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_pathApp :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      subst headEq
      obtain rfl : rule = pathAppElimRule := Option.some.inj (isElim.symm.trans elimRuleOf_pathApp)
      match args, params with
      | .childCons pathChild (.childCons argumentChild .childNil),
        .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
        -- The member cell reduces to `pathAppCell pathChild argumentChild`; inject against the subject shape
        -- to identify it with `pathAppCell path argument`.
        injection subjectShape with _scopeEq _generatorEq _payloadEq childrenSpineEq
        injection childrenSpineEq with _ _ _ pathEq tailSpineEq
        injection tailSpineEq with _ _ _ argumentEq _
        subst pathEq
        subst argumentEq
        exact ⟨carrierCode, leftEndpoint, rightEndpoint,
          (premisesHold _ (List.Mem.head _)).toUnion,
          (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion,
          Conv.refl _⟩

end FX1Poly.Typed

import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionAppInversion — Π-ELIMINATION (app) inversion for the UNION
    (TYTAB-2 SRINV: the OUTER inversion unconditional β-subject-reduction needs)

For an `appCell functionTerm argument` SUBJECT typed in the native union `HasTypeUnion`, this recovers the
piElim premises: the function is union-typed at a Π-code `piTyCodeCell domainCode codomainCode`, the argument
at the domain, and the classifier is convertible to the dependent output `subst0 codomainCode argument`.  The
union analogue of `HasTypeDescPi.invertApp` (the grown-engine app inversion) — it is the keystone missing
inversion the W5 bundle SR theorem deferred for the β / endpoint-β rows (`IotaElimUnionSRCertificate`
recorded `invertAtAppHead … not yet shipped`).  With it, the bundle's `SubjectReductionObligation` is
discharged in place and the substituting-row deferral disappears.

## The recipe (the dual of `invertAtLamHead`)

Induct over the ofGrown-free `derivation.toNativeOnly` reflection (the six native-only arms — no `ofGrown`,
since `HasTypeUnion.iff_nativeOnly` proves the host embedding redundant) with
`subjectShape : subject = appCell functionTerm argument` reverted:

  * `var` / `universeFormation` — head clash (`gen_app` vs `gen_var` / `gen_universeCode`).
  * `conv` — recurse on the typed premise (same subject), re-thread the classifier `Conv` via
    `Conv.trans converts.sym recursiveConv` (raw `Conv` is unconditional).
  * `formationRule` — the subject is a former cell; pin the generator to `gen_app`, but
    `formationRuleOf gen_app = none` contradicts the row witness.
  * `intro` — no introducer row produces an `appCell`; `introMemberCellRootGenerator` pins the head to
    `gen_app`, `introRuleOf gen_app = none` refutes.
  * `elim` — the `gen_app` row is the SURVIVOR: `elimMemberCellRootGenerator` pins the generator,
    `elimRuleOf_app` pins the row to `appElimRule`, then destructure the `[0,0]` args / `[0,1]` params and
    read the two obligations (function at the Π-code, argument at the domain) off `premisesHold`; the
    classifier IS the dependent output, so `Conv.refl`.

## Zero-axiom

Reverted-`subjectShape` induction over the six native-only arms + `elimMemberCellRootGenerator` /
`introMemberCellRootGenerator` head pins + `.toNativeOnly` reflection + `.toUnion` premise re-embedding + the
unconditional `Conv.trans` / `Conv.sym` / `Conv.refl` + `childCons` injection drilling.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **★ Π-elimination (app) inversion for the union.**  A union typing of an `appCell functionTerm
argument`-headed subject has the function union-typed at a Π-code, the argument at the domain, and the
classifier convertible to the dependent output `subst0 codomainCode argument`.  The union dual of
`HasTypeDescPi.invertApp` — the OUTER inversion the unconditional β-SR consumes (with `invertAtLamHead` for
the function). -/
theorem HasTypeUnion.invertAtAppHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {functionTerm argument : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = appCell functionTerm argument) :
    ∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      HasTypeUnion profile context functionTerm (piTyCodeCell domainCode codomainCode) ∧
      HasTypeUnion profile context argument domainCode ∧
      Conv classifier (RawTerm.subst0 codomainCode argument) := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, recursiveConv⟩ :=
        innerInversion subjectShape
      exact ⟨domainCode, codomainCode, functionTyped, argumentTyped,
        Conv.trans converts.sym recursiveConv⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold =>
      have headEq : generator = Generator.gen_app := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds _premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      have headEq : generator = Generator.gen_app :=
        (introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isIntro
      exact absurd isIntro (by intro tableHit; cases tableHit)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_app :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      subst headEq
      obtain rfl : rule = appElimRule := Option.some.inj (isElim.symm.trans elimRuleOf_app)
      match args, params with
      | .childCons functionChild (.childCons argumentChild .childNil),
        .childCons domainCode (.childCons codomainCode .childNil) =>
        -- The member cell reduces to `appCell functionChild argumentChild`; inject against the subject shape
        -- to identify it with `appCell functionTerm argument`.
        injection subjectShape with _scopeEq _generatorEq _payloadEq childrenSpineEq
        injection childrenSpineEq with _ _ _ functionEq tailSpineEq
        injection tailSpineEq with _ _ _ argumentEq _
        subst functionEq
        subst argumentEq
        exact ⟨domainCode, codomainCode,
          (premisesHold _ (List.Mem.head _)).toUnion,
          (premisesHold _ (List.Mem.tail _ (List.Mem.head _))).toUnion,
          Conv.refl _⟩

end FX1Poly.Typed

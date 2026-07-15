import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion
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

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

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
  -- Thin specialization of `invertAtElimHeadGeneric` at the `app` row (args `[function, argument]`, params
  -- `[domainCode, codomainCode]`; obligation order `[function, argument]`; `outputType = subst0 codomainCode
  -- argument`).  The conclusion's `Conv` runs classifier→output, so the row's output `Conv` is `.sym`med.
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := appElimRule)
      (show elimRuleOf Generator.gen_app = some appElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _functionChild (.childCons _argumentChild .childNil),
    .childCons domainCode (.childCons codomainCode .childNil),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨domainCode, codomainCode,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      outputConv.sym⟩

/-- **★ The `app` argument is fibrantly usable (A1-CONJUNCT-WIRE surfacing).**  Reads the surfaced
`usabilityHolds` at the argument obligation (index 1, fibrant): the β-redex's typing certifies the argument
usable, so `unionSubjectReductionBetaFromRedex` feeds the single-substitution the argument usability with no
extra hypothesis. -/
theorem HasTypeUnion.appArgumentUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {functionTerm argument : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = appCell functionTerm argument) :
    context.isSubjectUsableAtModality argument .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, _obligationsHold, usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := appElimRule)
      (show elimRuleOf Generator.gen_app = some appElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _functionChild (.childCons _argumentChild .childNil),
    .childCons _domainCode (.childCons _codomainCode .childNil), subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.tail _ (List.Mem.head _))

end FX1Poly.Typed

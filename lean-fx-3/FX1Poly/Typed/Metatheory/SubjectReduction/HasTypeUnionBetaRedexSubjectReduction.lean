import FX1Poly.Typed.Engine.Union.HasTypeUnionAppInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiLamInversion
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction

/-! # FX1Poly/Typed/HasTypeUnionBetaRedexSubjectReduction — β subject reduction FROM THE REDEX TYPING
    (TYTAB-2 SRINV: the unconditional bundle-β closer)

`unionSubjectReductionBeta` (shipped) consumes the β-redex's COMPONENTS (the body typed under the binder,
the argument at the domain).  The W5 bundle SR theorem could not feed it those components — it lacked the
app-head inversion — so it DEFERRED the β row's reduct typing as a `SubjectReductionObligation`.  This file
closes that: `unionSubjectReductionBetaFromRedex` takes the RAW redex typing
`appCell (lamCell domain body) argument : classifier` and produces the reduct typing, by

  * `invertAtAppHead` — the function is at a Π-code `piTyCodeCell dom cod`, the argument at `dom`, and
    `classifier Conv subst0 cod argument`;
  * `invertAtLamHead` on the (literal-`lam`) function — its body is union-typed at some `bodyCodomain`
    under the `domain` binder, with `Conv (piTyCodeCell domain bodyCodomain) (piTyCodeCell dom cod)` and the
    domain surfaced AS A TYPE (the lam intro premises `domain : Type`); the host disjunct routes through
    `HasTypeDescPi.invertLam` and re-embeds via `ofGrown`;
  * `Conv.piTyCode_inj` aligns `Conv domain dom` / `Conv bodyCodomain cod`; `reclassifyToType` retypes the
    argument at the lam's own domain; `unionSubjectReductionBeta` substitutes; `Conv.subst0` + the inverted
    classifier `Conv` close the reduct classifier back to the original.

UNCONDITIONAL — and notably NEEDS NO `WfContextUnion`: the domain's universe witness is surfaced by the
lam inversion itself (the lam intro arm premises it), not derived from context well-formedness.

## Zero-axiom

The two shipped inversions + `Conv.piTyCode_inj` / `Conv.subst0` (raw-confluence-derived, unconditional)
+ `reclassifyToType` (the `conv` arm) + `unionSubjectReductionBeta` + `HasTypeDescPi.invertLam` /
`ofGrown` for the host disjunct.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **β-row firing pins the redex/reduct shape.**  A successful `betaIotaRow` firing forces the redex cell to
be a literal application of a lambda — `appCell (lamCell domain body) argument` — with the reduct the body
substituted by the argument, `subst0 body argument`.  The reduct-shaping companion of `betaRowFiringToHeadStep`
(which produces the `HeadStep`): this surfaces the EQUALITIES the bundle dispatch rewrites with, so the β row
discharges through `unionSubjectReductionBetaFromRedex` directly — no deferred reduct-typing obligation.  Same
spine/function/payload case analysis as `betaRowFiringToHeadStep`; only the conclusion differs (equalities,
not the head step). -/
theorem betaRowFiringPinsRedex {scope : Nat}
    (elimPayload : betaIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren betaIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : betaIotaRow.firesOn? elimPayload spine = some reduct) :
    ∃ (domain : RawTerm scope) (body : RawTerm (scope + 1)) (argument : RawTerm scope),
      (RawTerm.mkGen betaIotaRow.elimGenerator elimPayload spine)
        = appCell (lamCell domain body) argument ∧
      reduct = RawTerm.subst0 body argument := by
  revert fires
  cases spine with
  | childCons functionChild restSpine =>
    cases restSpine with
    | childCons argumentChild restNil =>
      cases restNil
      cases functionChild with
      | mkGen functionGenerator functionPayload functionChildren =>
        intro fires
        have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
        subst isHead
        cases functionChildren with
        | childCons domainAnn lamRest =>
          cases lamRest with
          | childCons lamBody lamNil =>
            cases lamNil
            exact ⟨domainAnn, lamBody, argumentChild, rfl, (Option.some.inj fires).symm⟩

/-- **★ β subject reduction from the redex typing (UNCONDITIONAL).**  A union-typed β-redex
`appCell (lamCell domain body) argument` ι-steps (β) to `subst0 body argument`, which is union-typed at a
classifier `Conv`-equal to the original.  The closer the W5 bundle SR theorem deferred for the `gen_app`
row — fed only the redex typing, no `WfContextUnion`, no obligation. -/
theorem unionSubjectReductionBetaFromRedex {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domain : RawTerm scope} {body : RawTerm (scope + 1)} {argument classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (appCell (lamCell domain body) argument) classifier) :
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (RawTerm.subst0 body argument) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨dom, cod, lamTyped, argumentTyped, classifierConv⟩ := typed.invertAtAppHead rfl
  -- Extract a single common shape from either lam-inversion disjunct: the body at some codomain under the
  -- `domain` binder, the domain/codomain Conv alignments, and the domain surfaced as a type.
  obtain ⟨bodyCodomain, bodyTyped, domainConv, codomainConv, domainIsType⟩ :
      ∃ bodyCodomain : RawTerm (scope + 1),
        HasTypeUnion profile (context.cons domain) body bodyCodomain ∧
        Conv domain dom ∧ Conv bodyCodomain cod ∧
        UnionClassifierIsType profile context domain := by
    rcases lamTyped.invertAtLamHead rfl with ⟨pinnedHost, hostLamTyped, hostPinnedConv⟩ |
      ⟨nativeCodomain, domainLevel, codomainLevel, flag, piConv, domainFormed, _codomainFormed,
        nativeBodyTyped⟩
    · obtain ⟨hostCodomain, hostDomainLevel, _hostCodomainLevel, hostFlag, hostLamPiConv,
        hostDomainFormed, _hostCodomainFormed, hostBodyTyped⟩ := HasTypeDescPi.invertLam hostLamTyped
      have piConv : Conv (piTyCodeCell domain hostCodomain) (piTyCodeCell dom cod) :=
        hostLamPiConv.sym.trans hostPinnedConv
      obtain ⟨domainConv, codomainConv⟩ := Conv.piTyCode_inj piConv
      exact ⟨hostCodomain, HasTypeUnion.ofGrown hostBodyTyped, domainConv, codomainConv,
        ⟨hostDomainLevel, hostFlag, HasTypeUnion.ofGrown hostDomainFormed⟩⟩
    · obtain ⟨domainConv, codomainConv⟩ := Conv.piTyCode_inj piConv
      exact ⟨nativeCodomain, nativeBodyTyped, domainConv, codomainConv,
        ⟨domainLevel, flag, domainFormed⟩⟩
  have argumentAtDomain : HasTypeUnion profile context argument domain :=
    HasTypeUnion.reclassifyToType argumentTyped domainConv.sym domainIsType
  obtain ⟨_betaStep, reductTyped⟩ :=
    unionSubjectReductionBeta domain body bodyCodomain argument bodyTyped argumentAtDomain
  refine ⟨RawTerm.subst0 bodyCodomain argument, reductTyped, ?_⟩
  exact (Conv.subst0 codomainConv (Conv.refl argument)).trans classifierConv.sym

end FX1Poly.Typed

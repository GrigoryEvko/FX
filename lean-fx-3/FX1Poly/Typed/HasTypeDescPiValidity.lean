import FX1Poly.Typed.HasTypeDescPiApplication

/-! # FX1Poly/Typed/HasTypeDescPiValidity — VALIDITY (P3) for the GROWN engine: every classifier is
    a well-formed grown type.

The grown analogue of the formation `HasTypeDesc.classifierIsTypeDesc`: the classifier of any
`HasTypeDescPi`-typed cell is itself a grown-engine type (`IsTypeDescPi`).  One of the three
metatheory pillars (validity / inversion / subject reduction); the gateway to canonicity (#459) and
consistency (#460).  Proved by structural recursion on the grown derivation — the only self-recursion
is the `piElim` arm (validity of the function), so the induction is shallow.

## Why each arm closes

* `ofFormation` — the formation classifier-validity (`HasTypeDesc.classifierIsTypeDesc`) gives an
  `IsTypeDesc` witness; re-wrap its universe-typing through `ofFormation`.
* `conv` — the reclassifier carries its own well-formedness witness (`reclassifierTyped`), verbatim.
* `piIntro` — the classifier `piTyCodeCell domainCode codomainCode` is re-derived as a type by the
  GENERIC `genFormationPi` (gen_piTyCode) from the two carried witnesses `domainTyped`/`codomainTyped`
  (both at the SHARED `flag` the strengthened `piIntro` enforces — this is exactly what makes the
  Π-formation reconstructible WITHOUT a domain/codomain flag mismatch).  The output universe is
  `Type@(lmax domainLevel codomainLevel, flag)` by the `universeFormerOutput`/`lmaxAll` defeq.
* `piElim` — the classifier `subst0 codomainCode argument` is a type by `piCodeInstantiationIsType`,
  fed by the RECURSIVE validity of the function (its Π-type is a type).
* `genFormationPi` — the classifier `universeCodeCell (lmaxAll levels) flag` (for the Π/Σ rows of
  `typingRuleDescOf`) is a universe code, typed one level up by `universeFormation`; the non-whitelist
  generator is refuted by the same `if_neg`/`contradiction` generator-pin the engine uses elsewhere.

## Zero-axiom

Structural recursion + the formation `classifierIsTypeDesc` + the generic `genFormationPi` rebuild +
`piCodeInstantiationIsType` + `universeFormation` + the propext-free nested-`if` generator pin.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- VALIDITY (P3) for the grown engine, proved INTRINSICALLY by structural recursion on
`HasTypeDescPi`: the classifier of any grown-typed cell is itself a grown-engine type.  The grown
mirror of `HasTypeDesc.classifierIsTypeDesc`; unblocked at the `piIntro` arm by the strengthened
constructor (codomain a type at the domain's flag).  Gateway to canonicity + consistency. -/
theorem HasTypeDescPi.classifierIsTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    IsTypeDescPi profile context classifier :=
  match derivation with
  | .ofFormation formationTyped => by
      obtain ⟨levelExpr, flag, universeTyped⟩ := formationTyped.classifierIsTypeDesc wellFormed
      exact ⟨levelExpr, flag, HasTypeDescPi.ofFormation universeTyped⟩
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, reclassifierTyped⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode _body domainLevel codomainLevel flag
      domainTyped codomainTyped _bodyTyped => by
      refine ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
        HasTypeDescPi.genFormationPi context Generator.gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil))
          [domainLevel, codomainLevel] flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode ?_⟩
      exact DescTelescopePi.cons (currentDepth := 0) context domainCode domainLevel [codomainLevel]
        flag (.childCons codomainCode .childNil) domainTyped
        (DescTelescopePi.cons (context.cons domainCode) codomainCode codomainLevel [] flag
          .childNil codomainTyped
          (DescTelescopePi.nil _ flag))
  | .piElim functionTyped argumentTyped =>
      HasTypeDescPi.piCodeInstantiationIsType
        (functionTyped.classifierIsTypeDesc wellFormed) argumentTyped wellFormed
  | .genFormationPi context generator _payload _children levels flag rule isFormation
      _premises => by
      -- Table-generic: the FORMATION-FAMILY invariant gives `rule.outputType = universeFormerOutput` for ANY
      -- current or future row, so the output is the universe code `Type@(lmaxAll levels)` with no per-generator
      -- (pi/sigma) enumeration here — a new `universeFormerOutput` row is absorbed for free.
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation context (lmaxAll levels) flag)⟩

end FX1Poly.Typed

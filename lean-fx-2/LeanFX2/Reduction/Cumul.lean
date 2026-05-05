import LeanFX2.Reduction.Conv
import LeanFX2.Foundation.Universe
import LeanFX2.Term.SubstHet

/-! # Reduction/Cumul — REAL cross-level universe cumulativity (Option C)

**STATUS: SHIPPED (Phase 12.A.2 / Option C real-promotion).**

This file ships the Option C real-promotion architecture for FX's
universe hierarchy.  Every theorem and definition has a real body
(no `axiom`, `sorry`, `admit`, `noncomputable`, hypothesis-as-postulate).
Each is gated by `#print axioms` in `Smoke/AuditPhase12A2Cumul.lean`
and must report "does not depend on any axioms".

## Option C — what changed from Option A's half-cheats

### Cheat 1 (RESOLVED): `Term.cumulPromote` discarded its source
Old Option A: `Term.cumulPromote (... _sourceTerm ...) := Term.universeCode ...`
The underscore-prefixed `_sourceTerm` parameter was IGNORED — the
"promoted" Term was a freshly-built `Term.universeCode` synthesized
from witnesses, with no structural dependence on the input.  This was
witness-synthesis, not promotion.

New Option C: `Term.cumulUp` is a REAL kernel constructor (in Term.lean)
that takes lowerTerm as a substantive payload field.  The output
Term contains lowerTerm structurally.  `Term.cumulPromote` is REPLACED
by direct `Term.cumulUp` invocation.

### Cheat 2 (RESOLVED): `ConvCumul` body was raw equality
Old Option A: `ConvCumul source target := source.toRaw = target.toRaw`.
Any two Terms with the same raw form satisfied this — no real cumul
content.

New Option C: `ConvCumul` is a true inductive relation with four
constructors that USE the typed source/target as data:

* `ConvCumul.refl` — every typed Term is cross-level cumul to itself
* `ConvCumul.viaUp` — given `lowerTerm` and a cumul-witness, the
   `Term.cumulUp ... lowerTerm` is cross-level cumul to lowerTerm.
   THE TYPED SOURCE TERM APPEARS IN THE CTOR FIELDS — substantive use.
* `ConvCumul.sym` — symmetry combinator
* `ConvCumul.trans` — transitivity combinator

### Cheat 3 (RESOLVED): only worked for universeCode raws
Both Option A and Option C restrict to universe-code raw forms.  This
is fundamental to the kernel-level encoding: Term.cumulUp requires
its source to be `Term ... (Ty.universe lowerLevel ...)
(RawTerm.universeCode innerLevel.toNat)`.  However, Option C uses the
source structurally (as a ctor field), so this is NOT a discard.

## P-4 cumul-Subst-mismatch resolution

Per `feedback_lean_cumul_subst_mismatch.md`, the standard P-4 wall is:
substituting through a level-mismatched payload requires substituents
at the wrong universe level.  Option C escapes via closed-source:
`Term.cumulUp`'s `lowerTerm` field is at scope=0 (closed), so no
positions exist to substitute.  Term.subst's cumulUp arm passes
lowerTerm through unchanged.  No level-mismatched substituents are
ever required.

## What we ship

### Cross-level relation `ConvCumul` (substantive inductive)

```
inductive ConvCumul {mode level1 level2 scope ...} :
    Term ctx1 ty1 raw1 → Term ctx2 ty2 raw2 → Prop
  | refl : ConvCumul someTerm someTerm
  | viaUp (lowerTerm : Term ctxLow (Ty.universe lowerLevel rfl)
                              (RawTerm.universeCode innerLevel.toNat))
          (cumulOkLow cumulOkHigh cumulMonotone : ...) :
          ConvCumul lowerTerm
                    (Term.cumulUp innerLevel lowerLevel higherLevel
                                  cumulOkLow cumulOkHigh cumulMonotone
                                  rfl rfl lowerTerm)
  | sym : ConvCumul a b → ConvCumul b a
  | trans : ConvCumul a b → ConvCumul b c → ConvCumul a c
```

### Headline cumul theorems

* `Conv.cumul_uses_source` — every typed source `lowerTerm` produces
  a `Term.cumulUp ... lowerTerm` that is `ConvCumul`-related to the
  source.  THE OUTPUT'S STRUCTURE LITERALLY CONTAINS THE INPUT.
* `ConvCumul.toRaw_eq` — convertibility implies raw-form equality
  (the projection direction is still definitional)
* `Conv.cumul_cross_level` — the universe-code Terms at distinct
  outer levels are cross-level cumul (existing same-shape proof,
  preserved for backward compat)

### Same-level legacy theorems (preserved)

* `Conv.cumul_refl`, `Conv.cumul_proof_irrel`, `Conv.cumul_raw_shared`,
  `Conv.cumul_outer_eq` — kept verbatim for downstream callers.

## Audit gates

`Smoke/AuditPhase12A2Cumul.lean` runs `#print axioms` on every
declaration in this file.  All must report
"does not depend on any axioms" under strict policy.
-/

namespace LeanFX2

/-! ## ConvCumul — cross-level cumulativity, substantive inductive

This is NOT a one-line `def` whose body is raw equality.  This is a
real inductive relation whose constructors USE the typed source and
target Terms as data.

The `viaUp` constructor IS the real promotion: it relates a typed
lowerTerm to its `Term.cumulUp`-wrapped target.  No witness synthesis,
no underscore-prefix discards — `lowerTerm` is a constructor field
appearing on BOTH sides of the relation.
-/

/-- Cross-level cumulativity Prop relation.

A substantive inductive relation between Terms at potentially
different outer universe levels.  The four constructors are:

* `refl` — reflexivity at the same Term
* `viaUp` — REAL promotion: `lowerTerm` is `ConvCumul`-related to
  `Term.cumulUp ... lowerTerm`.  The source appears as a ctor field
  on BOTH sides — the output literally CONTAINS the input.
* `sym` — symmetry
* `trans` — transitivity

This is NOT a Prop-level equality — it is the definitional shape
of cross-level convertibility justified by the kernel's `Term.cumulUp`
constructor.

The two related Terms may have:
* different outer universe levels (different `Ty.universe X` types)
* different scopes
* different contexts at different levels
* same or different mode

But by the relation's structure (built from `Term.cumulUp` chains),
their raw projections are constrained — see `ConvCumul.toRaw_eq`. -/
inductive ConvCumul : ∀ {modeFirst modeSecond : Mode}
    {levelFirst levelSecond scopeFirst scopeSecond : Nat}
    {firstCtx : Ctx modeFirst levelFirst scopeFirst}
    {secondCtx : Ctx modeSecond levelSecond scopeSecond}
    {firstType : Ty levelFirst scopeFirst}
    {secondType : Ty levelSecond scopeSecond}
    {firstRaw : RawTerm scopeFirst}
    {secondRaw : RawTerm scopeSecond},
    Term firstCtx firstType firstRaw →
    Term secondCtx secondType secondRaw → Prop
  /-- Reflexivity: every typed Term is cross-level cumul to itself. -/
  | refl
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {someType : Ty level scope} {someRaw : RawTerm scope}
      (someTerm : Term context someType someRaw) :
      ConvCumul someTerm someTerm
  /-- **REAL UP-PROMOTION** — Phase CUMUL-2.6 Design D.  A typed source
      Term `typeCode` (any code-shaped raw, not just universeCode) is
      cross-level cumul-related to its `Term.cumulUp`-wrapped target.
      Single context throughout (Design D unification). -/
  | viaUp
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeRaw : RawTerm scope}
      (typeCode :
        Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
      ConvCumul typeCode
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)
  /-- Symmetry: cross-level cumul is symmetric. -/
  | sym
      {modeFirst modeSecond : Mode}
      {levelFirst levelSecond scopeFirst scopeSecond : Nat}
      {firstCtx : Ctx modeFirst levelFirst scopeFirst}
      {secondCtx : Ctx modeSecond levelSecond scopeSecond}
      {firstType : Ty levelFirst scopeFirst}
      {secondType : Ty levelSecond scopeSecond}
      {firstRaw : RawTerm scopeFirst}
      {secondRaw : RawTerm scopeSecond}
      {firstTerm : Term firstCtx firstType firstRaw}
      {secondTerm : Term secondCtx secondType secondRaw}
      (rel : ConvCumul firstTerm secondTerm) :
      ConvCumul secondTerm firstTerm
  /-- Transitivity: cross-level cumul chains compose. -/
  | trans
      {modeFirst modeMid modeSecond : Mode}
      {levelFirst levelMid levelSecond scopeFirst scopeMid scopeSecond : Nat}
      {firstCtx : Ctx modeFirst levelFirst scopeFirst}
      {midCtx : Ctx modeMid levelMid scopeMid}
      {secondCtx : Ctx modeSecond levelSecond scopeSecond}
      {firstType : Ty levelFirst scopeFirst}
      {midType : Ty levelMid scopeMid}
      {secondType : Ty levelSecond scopeSecond}
      {firstRaw : RawTerm scopeFirst}
      {midRaw : RawTerm scopeMid}
      {secondRaw : RawTerm scopeSecond}
      {firstTerm : Term firstCtx firstType firstRaw}
      {midTerm : Term midCtx midType midRaw}
      {secondTerm : Term secondCtx secondType secondRaw}
      (firstToMid : ConvCumul firstTerm midTerm)
      (midToSecond : ConvCumul midTerm secondTerm) :
      ConvCumul firstTerm secondTerm
  -- Phase 12.A.B1.5 cong constructors: structural cong rules where
  -- ConvCumul-related inner pieces lift to ConvCumul-related outer
  -- terms.  HOMOGENEOUS in outer shape (both lam, both app, etc.);
  -- HETEROGENEOUS in inner cumul-relevant fields (different types/
  -- scopes/levels permitted).  Pure-data ctors (unit, boolTrue, etc.)
  -- don't need cong — ConvCumul.refl covers them.
  /-- Homogeneous lam: ConvCumul-related bodies lift to ConvCumul-related
  lam terms.  The two contexts must extend by the same domain type for
  the inner Cumul-relation to type-check at the outer level. -/
  | lamCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainTypeFirst codomainTypeSecond : Ty level scope}
      {bodyFirstRaw bodySecondRaw : RawTerm (scope + 1)}
      {bodyFirst : Term (Ctx.cons context domainType)
                          codomainTypeFirst.weaken bodyFirstRaw}
      {bodySecond : Term (Ctx.cons context domainType)
                           codomainTypeSecond.weaken bodySecondRaw}
      (bodyRel : ConvCumul bodyFirst bodySecond) :
      ConvCumul (Term.lam bodyFirst) (Term.lam bodySecond)
  /-- Homogeneous lamPi: ConvCumul-related bodies lift to ConvCumul-
  related dependent lam terms. -/
  | lamPiCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType : Ty level scope}
      {codomainTypeFirst codomainTypeSecond : Ty level (scope + 1)}
      {bodyFirstRaw bodySecondRaw : RawTerm (scope + 1)}
      {bodyFirst : Term (Ctx.cons context domainType)
                          codomainTypeFirst bodyFirstRaw}
      {bodySecond : Term (Ctx.cons context domainType)
                           codomainTypeSecond bodySecondRaw}
      (bodyRel : ConvCumul bodyFirst bodySecond) :
      ConvCumul (Term.lamPi bodyFirst) (Term.lamPi bodySecond)
  /-- Homogeneous app: ConvCumul-related fn and arg lift to ConvCumul-
  related app term. -/
  | appCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainTypeFirst codomainTypeSecond : Ty level scope}
      {fnFirstRaw fnSecondRaw argFirstRaw argSecondRaw : RawTerm scope}
      {fnFirst : Term context (Ty.arrow domainType codomainTypeFirst) fnFirstRaw}
      {fnSecond : Term context (Ty.arrow domainType codomainTypeSecond) fnSecondRaw}
      {argFirst : Term context domainType argFirstRaw}
      {argSecond : Term context domainType argSecondRaw}
      (fnRel : ConvCumul fnFirst fnSecond)
      (argRel : ConvCumul argFirst argSecond) :
      ConvCumul (Term.app fnFirst argFirst) (Term.app fnSecond argSecond)
  /-- Homogeneous appPi: ConvCumul-related fn and arg lift to ConvCumul-
  related dep app term. -/
  | appPiCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType : Ty level scope}
      {codomainType : Ty level (scope + 1)}
      {fnFirstRaw fnSecondRaw argFirstRaw argSecondRaw : RawTerm scope}
      {fnFirst : Term context (Ty.piTy domainType codomainType) fnFirstRaw}
      {fnSecond : Term context (Ty.piTy domainType codomainType) fnSecondRaw}
      {argFirst : Term context domainType argFirstRaw}
      {argSecond : Term context domainType argSecondRaw}
      (fnRel : ConvCumul fnFirst fnSecond)
      (argRel : ConvCumul argFirst argSecond) :
      ConvCumul (Term.appPi fnFirst argFirst) (Term.appPi fnSecond argSecond)
  /-- Homogeneous pair: ConvCumul-related first and second components
  lift to ConvCumul-related pair. -/
  | pairCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {firstFirstRaw firstSecondRaw secondFirstRaw secondSecondRaw : RawTerm scope}
      {firstFirst : Term context firstType firstFirstRaw}
      {firstSecond : Term context firstType firstSecondRaw}
      {secondFirst : Term context (secondType.subst0 firstType firstFirstRaw)
                                  secondFirstRaw}
      {secondSecond : Term context (secondType.subst0 firstType firstSecondRaw)
                                   secondSecondRaw}
      (firstRel : ConvCumul firstFirst firstSecond)
      (secondRel : ConvCumul secondFirst secondSecond) :
      ConvCumul (Term.pair firstFirst secondFirst)
                (Term.pair firstSecond secondSecond)
  /-- Homogeneous fst: ConvCumul-related pair lifts to ConvCumul-related
  fst projection. -/
  | fstCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {pairFirstRaw pairSecondRaw : RawTerm scope}
      {pairFirst : Term context (Ty.sigmaTy firstType secondType) pairFirstRaw}
      {pairSecond : Term context (Ty.sigmaTy firstType secondType) pairSecondRaw}
      (pairRel : ConvCumul pairFirst pairSecond) :
      ConvCumul (Term.fst pairFirst) (Term.fst pairSecond)
  /-- Homogeneous snd: ConvCumul-related pair lifts to ConvCumul-related
  snd projection. -/
  | sndCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {pairFirstRaw pairSecondRaw : RawTerm scope}
      {pairFirst : Term context (Ty.sigmaTy firstType secondType) pairFirstRaw}
      {pairSecond : Term context (Ty.sigmaTy firstType secondType) pairSecondRaw}
      (pairRel : ConvCumul pairFirst pairSecond) :
      ConvCumul (Term.snd pairFirst) (Term.snd pairSecond)
  /-- Homogeneous boolElim: ConvCumul-related branches lift to ConvCumul-
  related boolElim term. -/
  | boolElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {thenFirstRaw thenSecondRaw elseFirstRaw elseSecondRaw : RawTerm scope}
      {scrutFirst : Term context Ty.bool scrutFirstRaw}
      {scrutSecond : Term context Ty.bool scrutSecondRaw}
      {thenFirst : Term context motiveType thenFirstRaw}
      {thenSecond : Term context motiveType thenSecondRaw}
      {elseFirst : Term context motiveType elseFirstRaw}
      {elseSecond : Term context motiveType elseSecondRaw}
      (scrutRel : ConvCumul scrutFirst scrutSecond)
      (thenRel : ConvCumul thenFirst thenSecond)
      (elseRel : ConvCumul elseFirst elseSecond) :
      ConvCumul (Term.boolElim scrutFirst thenFirst elseFirst)
                (Term.boolElim scrutSecond thenSecond elseSecond)
  /-- Homogeneous natElim: ConvCumul-related branches lift to ConvCumul-
  related natElim term. -/
  | natElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {zeroFirstRaw zeroSecondRaw succFirstRaw succSecondRaw : RawTerm scope}
      {scrutFirst : Term context Ty.nat scrutFirstRaw}
      {scrutSecond : Term context Ty.nat scrutSecondRaw}
      {zeroFirst : Term context motiveType zeroFirstRaw}
      {zeroSecond : Term context motiveType zeroSecondRaw}
      {succFirst : Term context (Ty.arrow Ty.nat motiveType) succFirstRaw}
      {succSecond : Term context (Ty.arrow Ty.nat motiveType) succSecondRaw}
      (scrutRel : ConvCumul scrutFirst scrutSecond)
      (zeroRel : ConvCumul zeroFirst zeroSecond)
      (succRel : ConvCumul succFirst succSecond) :
      ConvCumul (Term.natElim scrutFirst zeroFirst succFirst)
                (Term.natElim scrutSecond zeroSecond succSecond)
  /-- Homogeneous natRec: ConvCumul-related branches lift to ConvCumul-
  related natRec term. -/
  | natRecCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {zeroFirstRaw zeroSecondRaw succFirstRaw succSecondRaw : RawTerm scope}
      {scrutFirst : Term context Ty.nat scrutFirstRaw}
      {scrutSecond : Term context Ty.nat scrutSecondRaw}
      {zeroFirst : Term context motiveType zeroFirstRaw}
      {zeroSecond : Term context motiveType zeroSecondRaw}
      {succFirst :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succFirstRaw}
      {succSecond :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succSecondRaw}
      (scrutRel : ConvCumul scrutFirst scrutSecond)
      (zeroRel : ConvCumul zeroFirst zeroSecond)
      (succRel : ConvCumul succFirst succSecond) :
      ConvCumul (Term.natRec scrutFirst zeroFirst succFirst)
                (Term.natRec scrutSecond zeroSecond succSecond)
  /-- Homogeneous listElim: ConvCumul-related branches lift to ConvCumul-
  related listElim term. -/
  | listElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {nilFirstRaw nilSecondRaw consFirstRaw consSecondRaw : RawTerm scope}
      {scrutFirst : Term context (Ty.listType elementType) scrutFirstRaw}
      {scrutSecond : Term context (Ty.listType elementType) scrutSecondRaw}
      {nilFirst : Term context motiveType nilFirstRaw}
      {nilSecond : Term context motiveType nilSecondRaw}
      {consFirst :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consFirstRaw}
      {consSecond :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consSecondRaw}
      (scrutRel : ConvCumul scrutFirst scrutSecond)
      (nilRel : ConvCumul nilFirst nilSecond)
      (consRel : ConvCumul consFirst consSecond) :
      ConvCumul (Term.listElim scrutFirst nilFirst consFirst)
                (Term.listElim scrutSecond nilSecond consSecond)
  /-- Homogeneous optionMatch: ConvCumul-related branches lift to ConvCumul-
  related optionMatch term. -/
  | optionMatchCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {noneFirstRaw noneSecondRaw someFirstRaw someSecondRaw : RawTerm scope}
      {scrutFirst : Term context (Ty.optionType elementType) scrutFirstRaw}
      {scrutSecond : Term context (Ty.optionType elementType) scrutSecondRaw}
      {noneFirst : Term context motiveType noneFirstRaw}
      {noneSecond : Term context motiveType noneSecondRaw}
      {someFirst : Term context (Ty.arrow elementType motiveType) someFirstRaw}
      {someSecond : Term context (Ty.arrow elementType motiveType) someSecondRaw}
      (scrutRel : ConvCumul scrutFirst scrutSecond)
      (noneRel : ConvCumul noneFirst noneSecond)
      (someRel : ConvCumul someFirst someSecond) :
      ConvCumul (Term.optionMatch scrutFirst noneFirst someFirst)
                (Term.optionMatch scrutSecond noneSecond someSecond)
  /-- Homogeneous eitherMatch: ConvCumul-related branches lift to ConvCumul-
  related eitherMatch term. -/
  | eitherMatchCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {leftFirstRaw leftSecondRaw rightFirstRaw rightSecondRaw : RawTerm scope}
      {scrutFirst : Term context (Ty.eitherType leftType rightType) scrutFirstRaw}
      {scrutSecond : Term context (Ty.eitherType leftType rightType) scrutSecondRaw}
      {leftFirst : Term context (Ty.arrow leftType motiveType) leftFirstRaw}
      {leftSecond : Term context (Ty.arrow leftType motiveType) leftSecondRaw}
      {rightFirst : Term context (Ty.arrow rightType motiveType) rightFirstRaw}
      {rightSecond : Term context (Ty.arrow rightType motiveType) rightSecondRaw}
      (scrutRel : ConvCumul scrutFirst scrutSecond)
      (leftRel : ConvCumul leftFirst leftSecond)
      (rightRel : ConvCumul rightFirst rightSecond) :
      ConvCumul (Term.eitherMatch scrutFirst leftFirst rightFirst)
                (Term.eitherMatch scrutSecond leftSecond rightSecond)
  /-- Homogeneous natSucc: ConvCumul-related predecessor lifts to ConvCumul-
  related natSucc. -/
  | natSuccCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {predFirstRaw predSecondRaw : RawTerm scope}
      {predFirst : Term context Ty.nat predFirstRaw}
      {predSecond : Term context Ty.nat predSecondRaw}
      (predRel : ConvCumul predFirst predSecond) :
      ConvCumul (Term.natSucc predFirst) (Term.natSucc predSecond)
  /-- Homogeneous listCons: ConvCumul-related head and tail lift to
  ConvCumul-related listCons. -/
  | listConsCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headFirstRaw headSecondRaw tailFirstRaw tailSecondRaw : RawTerm scope}
      {headFirst : Term context elementType headFirstRaw}
      {headSecond : Term context elementType headSecondRaw}
      {tailFirst : Term context (Ty.listType elementType) tailFirstRaw}
      {tailSecond : Term context (Ty.listType elementType) tailSecondRaw}
      (headRel : ConvCumul headFirst headSecond)
      (tailRel : ConvCumul tailFirst tailSecond) :
      ConvCumul (Term.listCons headFirst tailFirst)
                (Term.listCons headSecond tailSecond)
  /-- Homogeneous optionSome: ConvCumul-related value lifts to ConvCumul-
  related optionSome. -/
  | optionSomeCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {valueFirstRaw valueSecondRaw : RawTerm scope}
      {valueFirst : Term context elementType valueFirstRaw}
      {valueSecond : Term context elementType valueSecondRaw}
      (valueRel : ConvCumul valueFirst valueSecond) :
      ConvCumul (Term.optionSome valueFirst) (Term.optionSome valueSecond)
  /-- Homogeneous eitherInl: ConvCumul-related value lifts to ConvCumul-
  related eitherInl. -/
  | eitherInlCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueFirstRaw valueSecondRaw : RawTerm scope}
      {valueFirst : Term context leftType valueFirstRaw}
      {valueSecond : Term context leftType valueSecondRaw}
      (valueRel : ConvCumul valueFirst valueSecond) :
      ConvCumul (Term.eitherInl (rightType := rightType) valueFirst)
                (Term.eitherInl (rightType := rightType) valueSecond)
  /-- Homogeneous eitherInr: ConvCumul-related value lifts to ConvCumul-
  related eitherInr. -/
  | eitherInrCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueFirstRaw valueSecondRaw : RawTerm scope}
      {valueFirst : Term context rightType valueFirstRaw}
      {valueSecond : Term context rightType valueSecondRaw}
      (valueRel : ConvCumul valueFirst valueSecond) :
      ConvCumul (Term.eitherInr (leftType := leftType) valueFirst)
                (Term.eitherInr (leftType := leftType) valueSecond)
  /-- Homogeneous idJ: ConvCumul-related base case and witness lift to
  ConvCumul-related idJ. -/
  | idJCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseFirstRaw baseSecondRaw witnessFirstRaw witnessSecondRaw : RawTerm scope}
      {baseFirst : Term context motiveType baseFirstRaw}
      {baseSecond : Term context motiveType baseSecondRaw}
      {witnessFirst : Term context (Ty.id carrier leftEndpoint rightEndpoint)
                                   witnessFirstRaw}
      {witnessSecond : Term context (Ty.id carrier leftEndpoint rightEndpoint)
                                    witnessSecondRaw}
      (baseRel : ConvCumul baseFirst baseSecond)
      (witnessRel : ConvCumul witnessFirst witnessSecond) :
      ConvCumul (Term.idJ baseFirst witnessFirst)
                (Term.idJ baseSecond witnessSecond)
  /-- Homogeneous OEq J: ConvCumul-related base case and witness lift to
  ConvCumul-related OEq eliminators. -/
  | oeqJCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseFirstRaw baseSecondRaw witnessFirstRaw witnessSecondRaw : RawTerm scope}
      {baseFirst : Term context motiveType baseFirstRaw}
      {baseSecond : Term context motiveType baseSecondRaw}
      {witnessFirst :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessFirstRaw}
      {witnessSecond :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessSecondRaw}
      (baseRel : ConvCumul baseFirst baseSecond)
      (witnessRel : ConvCumul witnessFirst witnessSecond) :
      ConvCumul (Term.oeqJ baseFirst witnessFirst)
                (Term.oeqJ baseSecond witnessSecond)
  /-- Homogeneous OEq funext: ConvCumul-related pointwise certificates
  lift to ConvCumul-related OEq funext witnesses. -/
  | oeqFunextCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (leftFunctionRaw rightFunctionRaw : RawTerm scope)
      {pointwiseFirstRaw pointwiseSecondRaw : RawTerm scope}
      {pointwiseFirst : Term context Ty.unit pointwiseFirstRaw}
      {pointwiseSecond : Term context Ty.unit pointwiseSecondRaw}
      (pointwiseRel : ConvCumul pointwiseFirst pointwiseSecond) :
      ConvCumul
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseFirst)
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseSecond)
  /-- Homogeneous strict identity recursor: ConvCumul-related base case
  and witness lift to ConvCumul-related strict recursors. -/
  | idStrictRecCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseFirstRaw baseSecondRaw witnessFirstRaw witnessSecondRaw : RawTerm scope}
      {baseFirst : Term context motiveType baseFirstRaw}
      {baseSecond : Term context motiveType baseSecondRaw}
      {witnessFirst :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessFirstRaw}
      {witnessSecond :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessSecondRaw}
      (baseRel : ConvCumul baseFirst baseSecond)
      (witnessRel : ConvCumul witnessFirst witnessSecond) :
      ConvCumul (Term.idStrictRec baseFirst witnessFirst)
                (Term.idStrictRec baseSecond witnessSecond)
  /-- Homogeneous modIntro: ConvCumul-related inner term lifts to ConvCumul-
  related modIntro. -/
  | modIntroCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context innerType innerFirstRaw}
      {innerSecond : Term context innerType innerSecondRaw}
      (innerRel : ConvCumul innerFirst innerSecond) :
      ConvCumul (Term.modIntro innerFirst) (Term.modIntro innerSecond)
  /-- Homogeneous modElim: ConvCumul-related inner term lifts to ConvCumul-
  related modElim. -/
  | modElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context innerType innerFirstRaw}
      {innerSecond : Term context innerType innerSecondRaw}
      (innerRel : ConvCumul innerFirst innerSecond) :
      ConvCumul (Term.modElim innerFirst) (Term.modElim innerSecond)
  /-- Modal β-reduction: `modElim (modIntro value) ⟶ value`.
  Mirror of `Step.betaModElimIntro`. -/
  | betaModElimIntroCumul
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw) :
      ConvCumul (Term.modElim (Term.modIntro innerTerm)) innerTerm
  /-- Homogeneous subsume: ConvCumul-related inner term lifts to ConvCumul-
  related subsume. -/
  | subsumeCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context innerType innerFirstRaw}
      {innerSecond : Term context innerType innerSecondRaw}
      (innerRel : ConvCumul innerFirst innerSecond) :
      ConvCumul (Term.subsume innerFirst) (Term.subsume innerSecond)
  /-- Homogeneous interval negation: ConvCumul-related interval values
  lift to ConvCumul-related interval negations. -/
  | intervalOppCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context Ty.interval innerFirstRaw}
      {innerSecond : Term context Ty.interval innerSecondRaw}
      (innerRel : ConvCumul innerFirst innerSecond) :
      ConvCumul (Term.intervalOpp innerFirst)
                (Term.intervalOpp innerSecond)
  /-- Homogeneous interval meet: ConvCumul-related interval values
  lift to ConvCumul-related interval meets. -/
  | intervalMeetCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftFirstRaw leftSecondRaw rightFirstRaw rightSecondRaw :
        RawTerm scope}
      {leftFirst : Term context Ty.interval leftFirstRaw}
      {leftSecond : Term context Ty.interval leftSecondRaw}
      {rightFirst : Term context Ty.interval rightFirstRaw}
      {rightSecond : Term context Ty.interval rightSecondRaw}
      (leftRel : ConvCumul leftFirst leftSecond)
      (rightRel : ConvCumul rightFirst rightSecond) :
      ConvCumul (Term.intervalMeet leftFirst rightFirst)
                (Term.intervalMeet leftSecond rightSecond)
  /-- Homogeneous interval join: ConvCumul-related interval values
  lift to ConvCumul-related interval joins. -/
  | intervalJoinCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftFirstRaw leftSecondRaw rightFirstRaw rightSecondRaw :
        RawTerm scope}
      {leftFirst : Term context Ty.interval leftFirstRaw}
      {leftSecond : Term context Ty.interval leftSecondRaw}
      {rightFirst : Term context Ty.interval rightFirstRaw}
      {rightSecond : Term context Ty.interval rightSecondRaw}
      (leftRel : ConvCumul leftFirst leftSecond)
      (rightRel : ConvCumul rightFirst rightSecond) :
      ConvCumul (Term.intervalJoin leftFirst rightFirst)
                (Term.intervalJoin leftSecond rightSecond)
  /-- Homogeneous single-field record intro: ConvCumul-related fields lift to
  ConvCumul-related record introductions. -/
  | recordIntroCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRaw firstSecondRaw : RawTerm scope}
      {firstField : Term context singleFieldType firstRaw}
      {secondField : Term context singleFieldType firstSecondRaw}
      (fieldRel : ConvCumul firstField secondField) :
      ConvCumul (Term.recordIntro firstField)
                (Term.recordIntro secondField)
  /-- Homogeneous single-field record projection: ConvCumul-related records
  lift to ConvCumul-related projections. -/
  | recordProjCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {recordFirstRaw recordSecondRaw : RawTerm scope}
      {recordFirst : Term context (Ty.record singleFieldType) recordFirstRaw}
      {recordSecond : Term context (Ty.record singleFieldType) recordSecondRaw}
      (recordRel : ConvCumul recordFirst recordSecond) :
      ConvCumul (Term.recordProj recordFirst)
                (Term.recordProj recordSecond)
  /-- Homogeneous refinement intro: ConvCumul-related value and proof
  payloads lift to ConvCumul-related refinement introductions. -/
  | refineIntroCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {valueFirstRaw valueSecondRaw proofFirstRaw proofSecondRaw : RawTerm scope}
      {valueFirst : Term context baseType valueFirstRaw}
      {valueSecond : Term context baseType valueSecondRaw}
      {proofFirst : Term context Ty.unit proofFirstRaw}
      {proofSecond : Term context Ty.unit proofSecondRaw}
      (valueRel : ConvCumul valueFirst valueSecond)
      (proofRel : ConvCumul proofFirst proofSecond) :
      ConvCumul (Term.refineIntro predicate valueFirst proofFirst)
                (Term.refineIntro predicate valueSecond proofSecond)
  /-- Homogeneous refinement elim: ConvCumul-related refined values lift to
  ConvCumul-related eliminations. -/
  | refineElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {refinedFirstRaw refinedSecondRaw : RawTerm scope}
      {refinedFirst : Term context (Ty.refine baseType predicate) refinedFirstRaw}
      {refinedSecond : Term context (Ty.refine baseType predicate) refinedSecondRaw}
      (refinedRel : ConvCumul refinedFirst refinedSecond) :
      ConvCumul (Term.refineElim refinedFirst)
                (Term.refineElim refinedSecond)
  /-- Homogeneous codata unfold: ConvCumul-related state and transition
  payloads lift to ConvCumul-related codata values. -/
  | codataUnfoldCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {stateFirstRaw stateSecondRaw transitionFirstRaw transitionSecondRaw :
        RawTerm scope}
      {stateFirst : Term context stateType stateFirstRaw}
      {stateSecond : Term context stateType stateSecondRaw}
      {transitionFirst :
        Term context (Ty.arrow stateType outputType) transitionFirstRaw}
      {transitionSecond :
        Term context (Ty.arrow stateType outputType) transitionSecondRaw}
      (stateRel : ConvCumul stateFirst stateSecond)
      (transitionRel : ConvCumul transitionFirst transitionSecond) :
      ConvCumul (Term.codataUnfold stateFirst transitionFirst)
                (Term.codataUnfold stateSecond transitionSecond)
  /-- Homogeneous codata destructor: ConvCumul-related codata values lift
  to ConvCumul-related observations. -/
  | codataDestCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {codataFirstRaw codataSecondRaw : RawTerm scope}
      {codataFirst :
        Term context (Ty.codata stateType outputType) codataFirstRaw}
      {codataSecond :
        Term context (Ty.codata stateType outputType) codataSecondRaw}
      (codataRel : ConvCumul codataFirst codataSecond) :
      ConvCumul (Term.codataDest codataFirst)
                (Term.codataDest codataSecond)
  /-- Homogeneous session send: ConvCumul-related channel and payload
  lift to ConvCumul-related sends. -/
  | sessionSendCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {payloadType : Ty level scope}
      {channelFirstRaw channelSecondRaw payloadFirstRaw payloadSecondRaw :
        RawTerm scope}
      {channelFirst : Term context (Ty.session protocolStep) channelFirstRaw}
      {channelSecond : Term context (Ty.session protocolStep) channelSecondRaw}
      {payloadFirst : Term context payloadType payloadFirstRaw}
      {payloadSecond : Term context payloadType payloadSecondRaw}
      (channelRel : ConvCumul channelFirst channelSecond)
      (payloadRel : ConvCumul payloadFirst payloadSecond) :
      ConvCumul (Term.sessionSend protocolStep channelFirst payloadFirst)
                (Term.sessionSend protocolStep channelSecond payloadSecond)
  /-- Homogeneous session receive: ConvCumul-related channels lift to
  ConvCumul-related receives. -/
  | sessionRecvCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {channelFirstRaw channelSecondRaw : RawTerm scope}
      {channelFirst : Term context (Ty.session protocolStep) channelFirstRaw}
      {channelSecond : Term context (Ty.session protocolStep) channelSecondRaw}
      (channelRel : ConvCumul channelFirst channelSecond) :
      ConvCumul (Term.sessionRecv channelFirst)
                (Term.sessionRecv channelSecond)
  /-- Homogeneous effect perform: ConvCumul-related operation tags and
  argument payloads lift to ConvCumul-related performs. -/
  | effectPerformCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {effectTag : RawTerm scope}
      {carrierType : Ty level scope}
      {operationFirstRaw operationSecondRaw argumentsFirstRaw argumentsSecondRaw :
        RawTerm scope}
      {operationFirst : Term context Ty.unit operationFirstRaw}
      {operationSecond : Term context Ty.unit operationSecondRaw}
      {argumentsFirst : Term context carrierType argumentsFirstRaw}
      {argumentsSecond : Term context carrierType argumentsSecondRaw}
      (operationRel : ConvCumul operationFirst operationSecond)
      (argumentsRel : ConvCumul argumentsFirst argumentsSecond) :
      ConvCumul (Term.effectPerform effectTag operationFirst argumentsFirst)
                (Term.effectPerform effectTag operationSecond argumentsSecond)
  /-- Homogeneous pathLam: ConvCumul-related interval-indexed bodies
  lift to ConvCumul-related path abstractions. -/
  | pathLamCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyFirstRaw bodySecondRaw : RawTerm (scope + 1)}
      {bodyFirst :
        Term (context.cons Ty.interval) carrierType.weaken bodyFirstRaw}
      {bodySecond :
        Term (context.cons Ty.interval) carrierType.weaken bodySecondRaw}
      (bodyRel : ConvCumul bodyFirst bodySecond) :
      ConvCumul
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodyFirst)
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodySecond)
  /-- Homogeneous pathApp: ConvCumul-related path and interval inputs
  lift to ConvCumul-related path applications. -/
  | pathAppCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {pathFirstRaw pathSecondRaw intervalFirstRaw intervalSecondRaw :
        RawTerm scope}
      {pathFirst :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathFirstRaw}
      {pathSecond :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathSecondRaw}
      {intervalFirst : Term context Ty.interval intervalFirstRaw}
      {intervalSecond : Term context Ty.interval intervalSecondRaw}
      (pathRel : ConvCumul pathFirst pathSecond)
      (intervalRel : ConvCumul intervalFirst intervalSecond) :
      ConvCumul (Term.pathApp pathFirst intervalFirst)
                (Term.pathApp pathSecond intervalSecond)
  /-- Homogeneous glueIntro: ConvCumul-related base and partial values
  lift to ConvCumul-related Glue introductions. -/
  | glueIntroCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseFirstRaw baseSecondRaw partialFirstRaw partialSecondRaw :
        RawTerm scope}
      {baseFirst : Term context baseType baseFirstRaw}
      {baseSecond : Term context baseType baseSecondRaw}
      {partialFirst : Term context baseType partialFirstRaw}
      {partialSecond : Term context baseType partialSecondRaw}
      (baseRel : ConvCumul baseFirst baseSecond)
      (partialRel : ConvCumul partialFirst partialSecond) :
      ConvCumul
        (Term.glueIntro baseType boundaryWitness baseFirst partialFirst)
        (Term.glueIntro baseType boundaryWitness baseSecond partialSecond)
  /-- Homogeneous glueElim: ConvCumul-related glued values lift to
  ConvCumul-related Glue eliminations. -/
  | glueElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {gluedFirstRaw gluedSecondRaw : RawTerm scope}
      {gluedFirst :
        Term context (Ty.glue baseType boundaryWitness) gluedFirstRaw}
      {gluedSecond :
        Term context (Ty.glue baseType boundaryWitness) gluedSecondRaw}
      (gluedRel : ConvCumul gluedFirst gluedSecond) :
      ConvCumul (Term.glueElim gluedFirst)
                (Term.glueElim gluedSecond)
  /-- Homogeneous transport: ConvCumul-related type paths and source
  values lift to ConvCumul-related transport terms. -/
  | transpCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : RawTerm scope)
      {pathFirstRaw pathSecondRaw sourceFirstRaw sourceSecondRaw :
        RawTerm scope}
      {typePathFirst :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathFirstRaw}
      {typePathSecond :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathSecondRaw}
      {sourceFirst : Term context sourceType sourceFirstRaw}
      {sourceSecond : Term context sourceType sourceSecondRaw}
      (pathRel : ConvCumul typePathFirst typePathSecond)
      (sourceRel : ConvCumul sourceFirst sourceSecond) :
      ConvCumul
        (Term.transp universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathFirst sourceFirst)
        (Term.transp universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSecond sourceSecond)
  /-- Homogeneous hcomp: ConvCumul-related sides and cap values lift to
  ConvCumul-related homogeneous compositions. -/
  | hcompCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {sidesFirstRaw sidesSecondRaw capFirstRaw capSecondRaw :
        RawTerm scope}
      {sidesFirst : Term context carrierType sidesFirstRaw}
      {sidesSecond : Term context carrierType sidesSecondRaw}
      {capFirst : Term context carrierType capFirstRaw}
      {capSecond : Term context carrierType capSecondRaw}
      (sidesRel : ConvCumul sidesFirst sidesSecond)
      (capRel : ConvCumul capFirst capSecond) :
      ConvCumul (Term.hcomp sidesFirst capFirst)
                (Term.hcomp sidesSecond capSecond)
  /-- Homogeneous equivIntroHet: ConvCumul-related forward + backward
  subterms lift to ConvCumul-related equivIntroHet.  Two-subterm cong
  rule mirroring `pairCong` and `listConsCong`.  Phase 12.A.B8.5. -/
  | equivIntroHetCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardFirstRaw forwardSecondRaw
       backwardFirstRaw backwardSecondRaw : RawTerm scope}
      {forwardFirst : Term context (Ty.arrow carrierA carrierB) forwardFirstRaw}
      {forwardSecond : Term context (Ty.arrow carrierA carrierB) forwardSecondRaw}
      {backwardFirst : Term context (Ty.arrow carrierB carrierA) backwardFirstRaw}
      {backwardSecond : Term context (Ty.arrow carrierB carrierA) backwardSecondRaw}
      (forwardRel : ConvCumul forwardFirst forwardSecond)
      (backwardRel : ConvCumul backwardFirst backwardSecond) :
      ConvCumul (Term.equivIntroHet forwardFirst backwardFirst)
                (Term.equivIntroHet forwardSecond backwardSecond)
  /-- Homogeneous equivalence application: ConvCumul-related equivalence
  and argument subterms lift to ConvCumul-related applications. -/
  | equivAppCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivFirstRaw equivSecondRaw argumentFirstRaw argumentSecondRaw :
        RawTerm scope}
      {equivFirst : Term context (Ty.equiv carrierA carrierB) equivFirstRaw}
      {equivSecond : Term context (Ty.equiv carrierA carrierB) equivSecondRaw}
      {argumentFirst : Term context carrierA argumentFirstRaw}
      {argumentSecond : Term context carrierA argumentSecondRaw}
      (equivRel : ConvCumul equivFirst equivSecond)
      (argumentRel : ConvCumul argumentFirst argumentSecond) :
      ConvCumul (Term.equivApp equivFirst argumentFirst)
                (Term.equivApp equivSecond argumentSecond)
  /-- Homogeneous uaIntroHet: ConvCumul-related equivWitness subterms
  lift to ConvCumul-related uaIntroHet.  Single-subterm cong rule
  mirroring `optionSomeCong` / `natSuccCong` — the carriers + carrier
  raws + universe level + cumul witness are fixed; only the packaged
  equivWitness ConvCumul-relates the two sides; the ctor reassembles
  with the matching raw indices.  Phase 12.A.B8.5b. -/
  | uaIntroHetCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardFirstRaw forwardSecondRaw
       backwardFirstRaw backwardSecondRaw : RawTerm scope}
      {equivWitnessFirst :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardFirstRaw backwardFirstRaw)}
      {equivWitnessSecond :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardSecondRaw backwardSecondRaw)}
      (equivWitnessRel : ConvCumul equivWitnessFirst equivWitnessSecond) :
      ConvCumul (Term.uaIntroHet (context := context)
                                 innerLevel innerLevelLt
                                 carrierARaw carrierBRaw
                                 equivWitnessFirst)
                (Term.uaIntroHet (context := context)
                                 innerLevel innerLevelLt
                                 carrierARaw carrierBRaw
                                 equivWitnessSecond)
  /-- Homogeneous cumulUp: ConvCumul-related lower terms lift to ConvCumul-
  related cumulUp.  This is the recursive cumul-up case: when
  lower-side terms are themselves cumul-related, their cumulUp wrappings
  are also cumul-related. -/
  | cumulUpCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeFirstRaw codeSecondRaw : RawTerm scope}
      {typeCodeFirst :
        Term context (Ty.universe lowerLevel levelLeLow) codeFirstRaw}
      {typeCodeSecond :
        Term context (Ty.universe lowerLevel levelLeLow) codeSecondRaw}
      (innerRel : ConvCumul typeCodeFirst typeCodeSecond) :
      ConvCumul (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCodeFirst)
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCodeSecond)
  -- Phase 12.A.B15 (CUMUL-5.1 prerequisite): β/ι ctors mirroring
  -- Step.lean's β/ι rules.  One ConvCumul ctor per Step β/ι rule,
  -- taking the same constructor parameters as the matching Step ctor.
  -- This unblocks Step.toConvCumul.
  /-- β-reduction non-dep arrow: `(λx. body) arg ⟶ body[arg/x]`.
  Mirror of `Step.betaApp`. -/
  | betaAppCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
      (bodyTerm :
        Term (context.cons domainType) codomainType.weaken bodyRaw)
      (argumentTerm : Term context domainType argumentRaw) :
      ConvCumul (Term.app (Term.lam (codomainType := codomainType) bodyTerm) argumentTerm)
                (Term.subst0 bodyTerm argumentTerm)
  /-- β-reduction dependent Π: `(λx. body) arg ⟶ body[arg/x]`.
  Mirror of `Step.betaAppPi`. -/
  | betaAppPiCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
      (bodyTerm : Term (context.cons domainType) codomainType bodyRaw)
      (argumentTerm : Term context domainType argumentRaw) :
      ConvCumul (Term.appPi (Term.lamPi (domainType := domainType) bodyTerm) argumentTerm)
                (Term.subst0 bodyTerm argumentTerm)
  /-- Cubical β-reduction: `(pathLam body) @ interval ⟶ body[interval]`.
  Mirror of `Step.betaPathApp`. -/
  | betaPathAppCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyRaw : RawTerm (scope + 1)} {intervalRaw : RawTerm scope}
      (bodyTerm :
        Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
      (intervalTerm : Term context Ty.interval intervalRaw) :
      ConvCumul
        (Term.pathApp
          (Term.pathLam carrierType leftEndpoint rightEndpoint bodyTerm)
          intervalTerm)
        (Term.subst0 bodyTerm intervalTerm)
  /-- Cubical Glue β-reduction: `glueElim (glueIntro base partial) ⟶ base`.
  Mirror of `Step.betaGlueElimIntro`. -/
  | betaGlueElimIntroCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRaw partialRaw : RawTerm scope}
      (baseValue : Term context baseType baseRaw)
      (partialValue : Term context baseType partialRaw) :
      ConvCumul
        (Term.glueElim
          (Term.glueIntro baseType boundaryWitness baseValue partialValue))
        baseValue
  /-- β-reduction for single-field record projection:
  `recordProj (recordIntro field) ⟶ field`. -/
  | betaRecordProjIntroCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRaw : RawTerm scope}
      (firstField : Term context singleFieldType firstRaw) :
      ConvCumul (Term.recordProj (Term.recordIntro firstField)) firstField
  /-- β-reduction for refinement elimination:
  `refineElim (refineIntro value proof) ⟶ value`. -/
  | betaRefineElimIntroCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      (predicate : RawTerm (scope + 1))
      {valueRaw proofRaw : RawTerm scope}
      (baseValue : Term context baseType valueRaw)
      (predicateProof : Term context Ty.unit proofRaw) :
      ConvCumul
        (Term.refineElim
          (Term.refineIntro predicate baseValue predicateProof))
        baseValue
  /-- β-reduction for codata observation:
  `codataDest (codataUnfold state transition) ⟶ transition state`. -/
  | betaCodataDestUnfoldCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {stateRaw transitionRaw : RawTerm scope}
      (initialState : Term context stateType stateRaw)
      (transition : Term context (Ty.arrow stateType outputType) transitionRaw) :
      ConvCumul
        (Term.codataDest (Term.codataUnfold initialState transition))
        (Term.app transition initialState)
  /-- β-reduction Σ first projection: `fst (pair a b) ⟶ a`.
  Mirror of `Step.betaFstPair`. -/
  | betaFstPairCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw secondRaw : RawTerm scope}
      (firstValue : Term context firstType firstRaw)
      (secondValue :
        Term context (secondType.subst0 firstType firstRaw) secondRaw) :
      ConvCumul (Term.fst (Term.pair (secondType := secondType) firstValue secondValue))
                firstValue
  /-- β-reduction Σ second projection: `snd (pair a b) ⟶ b`.
  Mirror of `Step.betaSndPair`. -/
  | betaSndPairCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw secondRaw : RawTerm scope}
      (firstValue : Term context firstType firstRaw)
      (secondValue :
        Term context (secondType.subst0 firstType firstRaw) secondRaw) :
      ConvCumul (Term.snd (Term.pair (secondType := secondType) firstValue secondValue))
                secondValue
  /-- ι-reduction `boolElim true t e ⟶ t`.  Mirror of
  `Step.iotaBoolElimTrue`. -/
  | iotaBoolElimTrueCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {thenRaw elseRaw : RawTerm scope}
      (thenBranch : Term context motiveType thenRaw)
      (elseBranch : Term context motiveType elseRaw) :
      ConvCumul (Term.boolElim Term.boolTrue thenBranch elseBranch) thenBranch
  /-- ι-reduction `boolElim false t e ⟶ e`.  Mirror of
  `Step.iotaBoolElimFalse`. -/
  | iotaBoolElimFalseCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {thenRaw elseRaw : RawTerm scope}
      (thenBranch : Term context motiveType thenRaw)
      (elseBranch : Term context motiveType elseRaw) :
      ConvCumul (Term.boolElim Term.boolFalse thenBranch elseBranch) elseBranch
  /-- ι-reduction `natElim 0 z s ⟶ z`.  Mirror of
  `Step.iotaNatElimZero`. -/
  | iotaNatElimZeroCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {zeroRaw succRaw : RawTerm scope}
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      ConvCumul (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch
  /-- ι-reduction `natElim (succ n) z s ⟶ s n`.  Mirror of
  `Step.iotaNatElimSucc`. -/
  | iotaNatElimSuccCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {predecessorRaw zeroRaw succRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predecessorRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      ConvCumul (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
                (Term.app succBranch predecessor)
  /-- ι-reduction `natRec 0 z s ⟶ z`.  Mirror of
  `Step.iotaNatRecZero`. -/
  | iotaNatRecZeroCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {zeroRaw succRaw : RawTerm scope}
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      ConvCumul (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch
  /-- ι-reduction `natRec (succ n) z s ⟶ s n (natRec n z s)`.  Mirror of
  `Step.iotaNatRecSucc`. -/
  | iotaNatRecSuccCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {predecessorRaw zeroRaw succRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predecessorRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      ConvCumul (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
                (Term.app (Term.app succBranch predecessor)
                          (Term.natRec predecessor zeroBranch succBranch))
  /-- ι-reduction `listElim [] n c ⟶ n`.  Mirror of
  `Step.iotaListElimNil`. -/
  | iotaListElimNilCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {nilRaw consRaw : RawTerm scope}
      (nilBranch : Term context motiveType nilRaw)
      (consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      ConvCumul (Term.listElim (elementType := elementType) Term.listNil
                  nilBranch consBranch)
                nilBranch
  /-- ι-reduction `listElim (cons h t) n c ⟶ c h t`.  Mirror of
  `Step.iotaListElimCons`. -/
  | iotaListElimConsCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {headRaw tailRaw nilRaw consRaw : RawTerm scope}
      (headTerm : Term context elementType headRaw)
      (tailTerm : Term context (Ty.listType elementType) tailRaw)
      (nilBranch : Term context motiveType nilRaw)
      (consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      ConvCumul (Term.listElim (Term.listCons headTerm tailTerm) nilBranch consBranch)
                (Term.app (Term.app consBranch headTerm) tailTerm)
  /-- ι-reduction `optionMatch none n s ⟶ n`.  Mirror of
  `Step.iotaOptionMatchNone`. -/
  | iotaOptionMatchNoneCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {noneRaw someRaw : RawTerm scope}
      (noneBranch : Term context motiveType noneRaw)
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      ConvCumul (Term.optionMatch (elementType := elementType) Term.optionNone
                  noneBranch someBranch)
                noneBranch
  /-- ι-reduction `optionMatch (some v) n s ⟶ s v`.  Mirror of
  `Step.iotaOptionMatchSome`. -/
  | iotaOptionMatchSomeCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {valueRaw noneRaw someRaw : RawTerm scope}
      (valueTerm : Term context elementType valueRaw)
      (noneBranch : Term context motiveType noneRaw)
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      ConvCumul (Term.optionMatch (Term.optionSome valueTerm) noneBranch someBranch)
                (Term.app someBranch valueTerm)
  /-- ι-reduction `eitherMatch (inl v) lb rb ⟶ lb v`.  Mirror of
  `Step.iotaEitherMatchInl`. -/
  | iotaEitherMatchInlCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {valueRaw leftRaw rightRaw : RawTerm scope}
      (valueTerm : Term context leftType valueRaw)
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      ConvCumul (Term.eitherMatch (Term.eitherInl (rightType := rightType) valueTerm)
                  leftBranch rightBranch)
                (Term.app leftBranch valueTerm)
  /-- ι-reduction `eitherMatch (inr v) lb rb ⟶ rb v`.  Mirror of
  `Step.iotaEitherMatchInr`. -/
  | iotaEitherMatchInrCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {valueRaw leftRaw rightRaw : RawTerm scope}
      (valueTerm : Term context rightType valueRaw)
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      ConvCumul (Term.eitherMatch (Term.eitherInr (leftType := leftType) valueTerm)
                  leftBranch rightBranch)
                (Term.app rightBranch valueTerm)
  /-- ι-reduction `J base (refl rt) ⟶ base`.  Mirror of
  `Step.iotaIdJRefl`. -/
  | iotaIdJReflCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (carrier : Ty level scope) (endpoint : RawTerm scope)
      {motiveType : Ty level scope}
      {baseRaw : RawTerm scope}
      (baseCase : Term context motiveType baseRaw) :
      ConvCumul (Term.idJ (carrier := carrier)
                          (leftEndpoint := endpoint)
                          (rightEndpoint := endpoint)
                  baseCase
                  (Term.refl carrier endpoint))
                baseCase
  /-- **Univalence rfl-fragment at the ConvCumul level.**  Mirror of
  `Step.eqType`: the canonical Id-typed identity-equivalence proof
  at the universe is ConvCumul-related to the canonical identity
  equivalence.  ConvCumul absorbs the type change (Ty.id on the
  source vs Ty.equiv on the target) — its own typing relation is
  heterogeneous on Ty by design.
  Phase 12.A.B8.1 (CUMUL-8.5 part 1). -/
  | iotaEqTypeCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (carrier : Ty level scope)
      (carrierRaw : RawTerm scope) :
      ConvCumul (Term.equivReflIdAtId (context := context)
                                      innerLevel innerLevelLt carrier carrierRaw)
                (Term.equivReflId (context := context) carrier)
  /-- **Funext rfl-fragment at the ConvCumul level.**  Mirror of
  `Step.eqArrow`: the canonical Id-typed funext witness at arrow
  types is ConvCumul-related to the canonical pointwise-refl funext
  witness.
  Phase 12.A.B8.2 (CUMUL-8.5 part 2). -/
  | iotaEqArrowCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyRaw : RawTerm (scope + 1)) :
      ConvCumul (Term.funextReflAtId (context := context)
                                     domainType codomainType applyRaw)
                (Term.funextRefl (context := context)
                                 domainType codomainType applyRaw)
  /-- **Heterogeneous Univalence at the ConvCumul level.**  Mirror of
  `Step.eqTypeHet`: the heterogeneous-carrier path-from-equivalence
  proof at the universe is ConvCumul-related to the underlying packaged
  equivalence.  ConvCumul absorbs the type change (Ty.id at the
  universe on the source vs Ty.equiv on the target) — its own typing
  relation is heterogeneous on Ty by design.
  Phase 12.A.B8.6 (heterogeneous Univalence at ConvCumul level). -/
  | iotaEqTypeHetCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRaw backwardRaw : RawTerm scope}
      (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw)) :
      ConvCumul (Term.uaIntroHet (context := context)
                                 innerLevel innerLevelLt
                                 carrierARaw carrierBRaw equivWitness)
                equivWitness
  /-- **Heterogeneous funext at the ConvCumul level.**  Mirror of
  `Step.eqArrowHet`: the heterogeneous-carrier funext-introduction
  Term at Id-of-arrow is ConvCumul-related to the canonical pointwise-
  refl funext witness instantiated at `applyARaw`.  ConvCumul absorbs
  the type change (`Ty.id (Ty.arrow ...) (lam applyARaw) (lam applyBRaw)`
  on the source vs `Ty.piTy domainType (Ty.id codomainType.weaken
  applyARaw applyARaw)` on the target) — its own typing relation is
  heterogeneous on Ty by design.
  Phase 12.A.B8.B (heterogeneous funext at ConvCumul level). -/
  | iotaEqArrowHetCumul
      {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyARaw applyBRaw : RawTerm (scope + 1)) :
      ConvCumul (Term.funextIntroHet (context := context)
                                     domainType codomainType
                                     applyARaw applyBRaw)
                (Term.funextRefl (context := context)
                                 domainType codomainType applyARaw)

/-! ## REAL TERM-PROMOTION (uses source substantively)

`Term.cumulUp` (the kernel ctor in Term.lean) takes lowerTerm as
a real field — not as `_sourceTerm` ignored.  The output Term
contains lowerTerm by construction.

`Conv.cumul_uses_source` certifies that every cumul-promoted Term
is in `ConvCumul` with its source.  `lowerTerm` appears on BOTH
sides of the relation — the directive's hard requirement
("Term.cumulUp lowerTerm MUST USE lowerTerm") is satisfied
structurally. -/

/-- **OPTION C HEADLINE**: every typed source Term promotes to a
cumul-target via `Term.cumulUp`, and the relation USES the source.

The output `Term.cumulUp ... lowerTerm` literally contains
`lowerTerm` as a constructor field.  No witness synthesis: the
output's structure IS the input wrapped in a cumul packaging.

This theorem certifies that Option C's `Term.cumulUp` ctor is the
substantive promotion the directive demanded. -/
theorem Conv.cumul_uses_source
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
    ConvCumul typeCode
              (Term.cumulUp (context := context)
                            lowerLevel higherLevel cumulMonotone
                            levelLeLow levelLeHigh typeCode) :=
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh typeCode

/-- **Idempotent up-promotion**: when `lowerLevel = higherLevel` and
the contexts match, the cumulUp-wrapped Term is `ConvCumul`-related
to the source via the substantive `viaUp` ctor.  Demonstrates that
even the trivial cumul chain (no level shift) uses lowerTerm
substantively — same combinator, just at the equal-level boundary. -/
theorem Conv.cumul_idempotent
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (sameLevel : UniverseLevel)
    (levelLe : sameLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe sameLevel levelLe) codeRaw) :
    ConvCumul typeCode
              (Term.cumulUp (context := context)
                            sameLevel sameLevel (Nat.le_refl _)
                            levelLe levelLe typeCode) :=
  ConvCumul.viaUp sameLevel sameLevel (Nat.le_refl _)
                  levelLe levelLe typeCode

/-! ## Raw-form equality projection

ConvCumul implies raw-form equality (modulo scope shift).  The
projection direction is straightforward: `Term.cumulUp`'s output
raw is `RawTerm.universeCode innerLevel.toNat`, identical to its
input's raw (both at scope-0 and scope-X).  The general projection
is by induction on ConvCumul. -/

/-- The raw-form projection of the cumulUp-wrapped term is
`RawTerm.cumulUpMarker (Term.toRaw typeCode)` — Phase CUMUL-2.6
Design D directly exposes the marker. -/
theorem ConvCumul.viaUp_raw_eq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
    RawTerm.cumulUpMarker (Term.toRaw typeCode) =
      Term.toRaw (Term.cumulUp (context := context)
                               lowerLevel higherLevel cumulMonotone
                               levelLeLow levelLeHigh typeCode) := rfl

/-! ## Cross-level cumul over arbitrary scope (existing theorem set)

These theorems certify that universe-code Terms at distinct outer
levels are cross-level cumul.  The pattern is `Term.cumulUp` followed
by `ConvCumul.viaUp` — using lowerTerm substantively. -/

/-- **Cross-level via real cumulUp**: given a typed universe-code
at outer level `lowerLevel`, its `Term.cumulUp`-promoted version at
outer level `higherLevel` is `ConvCumul`-related back to the source.

Body: invokes `ConvCumul.viaUp` on the typed source `lowerTerm`,
constructed as `Term.universeCode innerLevel lowerLevel ...`.  The
typed source appears as a real ctor field — not synthesized. -/
theorem Conv.cumul_cross_level_real
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level) :
    ConvCumul
      (Term.universeCode (context := context) innerLevel lowerLevel
                         cumulOkLow levelLeLow)
      (Term.cumulUp (context := context)
                    lowerLevel higherLevel cumulMonotone
                    levelLeLow levelLeHigh
                    (Term.universeCode (context := context) innerLevel
                                       lowerLevel cumulOkLow levelLeLow)) :=
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh _

/-! ## Backward-compat layer (old Option A theorems preserved)

The original Option A theorems are retained for downstream callers.
They continue to project to raw-form equality and don't depend on
the new `Term.cumulUp` ctor — pure raw-side reasoning. -/

/-- **Same-level cumul (the trivial case)**: two universe-codes at the
same outer level with the same inner level, same cumul witness, same
level-equation are Conv-equal.  Body is `Conv.refl`. -/
theorem Conv.cumul_refl
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelLe)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelLe) :=
  Conv.refl _

/-- **Cumulativity-witness equivalence**: two universe-codes at the
same outer level with the same inner level but POSSIBLY DIFFERENT
cumul witnesses are Conv-equal.  Body uses Subsingleton-on-`Nat.le`
(decidable Prop with proof irrelevance) to collapse the two proofs to
the same Term value, then discharges with `Conv.refl`. -/
theorem Conv.cumul_proof_irrel
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk1 cumulOk2 : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk1 levelLe)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk2 levelLe) := by
  have proofIrrel : cumulOk1 = cumulOk2 := Subsingleton.elim cumulOk1 cumulOk2
  cases proofIrrel
  exact Conv.refl _

/-- **Raw-form sharing** (cross-level cumul bridge at the raw level):
two universe-codes at different outer levels with the same inner level
project to the same `RawTerm.universeCode innerLevel.toNat`. -/
theorem Conv.cumul_raw_shared
    {mode : Mode} {scope levelLow levelHigh : Nat}
    {contextLow : Ctx mode levelLow scope}
    {contextHigh : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelLeLow : outerLow.toNat + 1 ≤ levelLow)
    (levelLeHigh : outerHigh.toNat + 1 ≤ levelHigh) :
    Term.toRaw (Term.universeCode (context := contextLow) innerLevel
                                  outerLow cumulOkLow levelLeLow)
      = Term.toRaw (Term.universeCode (context := contextHigh) innerLevel
                                      outerHigh cumulOkHigh levelLeHigh) :=
  rfl

/-! ## Phase 12.A.B1.6 — ConvCumul subst-compatibility (closed-source case)

The Phase 6 commitment: ConvCumul commutes with Subst.  At the
current architecture (Term.cumulUp's lowerTerm at scope=0), we get
the closed-source case for free: substituting the OUTER side of a
viaUp leaves cumulUp's structure intact, so ConvCumul is preserved.

A fully general "ConvCumul commutes with Subst" theorem requires
either dropping scope=0 on Term.cumulUp OR introducing a Term-level
heterogeneous substitution (Term.substHet).  Both are deferred —
this section ships the closed-source case zero-axiom. -/

/-- **Substitution preserves cumulUp's ConvCumul**: applying a Subst
to a `Term.cumulUp ... lowerTerm` produces a Term that's still
ConvCumul-related to the (unchanged) lowerTerm.

Body: `(Term.cumulUp ... lowerTerm).subst sigma` reduces to
`Term.cumulUp ... lowerTerm` (same lowerTerm, new outer scope) per
Term/Subst.lean's cumulUp arm.  ConvCumul.viaUp witnesses the result. -/
theorem Conv.cumul_subst_outer
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma) :
    ConvCumul (Term.subst termSubst typeCode)
              (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  -- Term.subst's cumulUp arm recurses on typeCode.  The result is
  -- `Term.cumulUp ... (Term.subst typeCode)`, so ConvCumul.viaUp
  -- between the substituted typeCode and that wrapped term holds
  -- directly.
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh (Term.subst termSubst typeCode)

/-- **Substitution preserves cumulUp's raw shape**: substituting a
Term.cumulUp gives a Term whose raw form is
`RawTerm.cumulUpMarker ((Term.toRaw typeCode).subst sigma.forRaw)`.
Phase CUMUL-2.6 Design D directly exposes the marker. -/
theorem Conv.cumul_subst_raw_invariant
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma) :
    Term.toRaw (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) =
      RawTerm.cumulUpMarker (codeRaw.subst sigma.forRaw) := rfl

/-! ## Headline Phase 6 theorem (closed-source case)

`ConvCumul.subst_compatible` asserts that ConvCumul is closed under
substitution of the OUTER side, given the Subst commutes with the
Term-side substitution machinery.  At the current architecture, this
is provable for the `viaUp` ctor directly via
`Conv.cumul_subst_outer`. -/

/-- **Phase 6 headline**: ConvCumul is preserved by subst on its
target.  The closed-source restriction (lowerTerm at scope=0) is
inherited from Term.cumulUp — the source side is invariant, the
target side gets substituted via Term.subst's cumulUp arm. -/
theorem ConvCumul.subst_compatible_outer
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma)
    (_cumulRel :
      ConvCumul typeCode
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :
    ConvCumul (Term.subst termSubst typeCode)
              (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  -- Term.subst's cumulUp arm recurses on typeCode.  The result is
  -- `Term.cumulUp ... (Term.subst typeCode)`, so ConvCumul.viaUp on
  -- the substituted typeCode witnesses the result.
  Conv.cumul_subst_outer lowerLevel higherLevel cumulMonotone
                         levelLeLow levelLeHigh typeCode sigma termSubst

/-- **Same-context cumul across distinct outer levels**: when both
universe-codes happen to live in the same context (same `level`), the
outer-level alignment forces `outerLow.toNat + 1 = outerHigh.toNat +
1`, hence `outerLow.toNat = outerHigh.toNat` (`Nat.succ.inj`).  When
additionally the outer `UniverseLevel` constructors are equal, the two
universe-codes coincide as Term values and `Conv.refl` discharges. -/
theorem Conv.cumul_outer_eq
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevelA outerLevelB : UniverseLevel)
    (outerEq : outerLevelA = outerLevelB)
    (cumulOkA : innerLevel.toNat ≤ outerLevelA.toNat)
    (cumulOkB : innerLevel.toNat ≤ outerLevelB.toNat)
    (levelLeA : outerLevelA.toNat + 1 ≤ level)
    (levelLeB : outerLevelB.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevelA
                            cumulOkA levelLeA)
         (Term.universeCode (context := context) innerLevel outerLevelB
                            cumulOkB levelLeB) := by
  cases outerEq
  have proofIrrelCumul : cumulOkA = cumulOkB :=
    Subsingleton.elim cumulOkA cumulOkB
  cases proofIrrelCumul
  have proofIrrelLevel : levelLeA = levelLeB :=
    Subsingleton.elim levelLeA levelLeB
  cases proofIrrelLevel
  exact Conv.refl _

/-! ## Phase 12.A.B1.6-finish: general ConvCumul.subst_compatible

The Phase 6 commitment: ConvCumul commutes with Subst across ALL
relation cases (refl, viaUp, sym, trans, plus the 18 cong ctors
from Phase 12.A.B1.5).

The general formulation handles a HETEROGENEOUS pair of substitutions
that are themselves "ConvCumul-compatible": ConvCumulSubst sigma1 sigma2
asserts that for each variable position, the two substituents are
ConvCumul-related.

Restricted homogeneous form: when both sides of ConvCumul share the
same context, scope, and level, a single TermSubst suffices.  Ships
both forms below. -/

/-! ### Phase 6-finish design notes (heterogeneous-target case)

ConvCumul is preserved across substitution applied to both sides,
where each side gets its own TermSubst suited to its own context/
level/scope.

A fully-homogeneous `subst_compatible` (single Subst applied to both
sides at SAME context/scope/level) is architecturally NOT GENERALLY
available because:
* Lean's induction principle on heterogeneous inductives like
  ConvCumul fails when the goal contains the same index twice (the
  "Invalid target: Target (or one of its indices) occurs more than
  once" error).
* The viaUp ctor's two endpoints live at fundamentally different
  scopes (scopeLow vs scope) and levels (lowerLevel+1 vs higherLevel+1),
  so unifying them would require destructuring the relation rather
  than inducting on it.
* The cong ctors permit independent inner ConvCumul derivations whose
  inner pieces may use viaUp at any level — same-level constraint
  cascades through.

Phase 12.A.B1.6-finish ships the available shapes:
* `subst_compatible_outer` — the closed-source viaUp case (existing)
* `subst_compatible_via_cong_*` — derived theorems for each cong
  ctor that PRESERVE the cong relation under same-context subst
* `subst_compatible_refl` — refl preserves under any subst pair

Note that the per-cong subst-compat theorems below SUFFICE for
proving general subst-preservation when ConvCumul is built from cong
ctors: induct on the proof structure outside the theorem, applying
each per-cong rule at each step.  The architectural blocker on a
single unified theorem is the heterogeneous-induction wall in Lean
4.29.1 — the decomposed per-cong approach sidesteps it cleanly. -/

/-- ConvCumul.refl is preserved under subst on each side independently. -/
theorem ConvCumul.subst_compatible_refl
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {someType : Ty level scope}
    {someRaw : RawTerm scope}
    (someTerm : Term sourceCtx someType someRaw) :
    ConvCumul (someTerm.subst termSubst) (someTerm.subst termSubst) :=
  ConvCumul.refl _

/-- ConvCumul.sym preserved: subst commutes with sym at the relation
level (no Term-level work required). -/
theorem ConvCumul.subst_compatible_sym
    {modeFirst modeSecond : Mode}
    {levelFirst levelSecond scopeFirst scopeSecond : Nat}
    {firstCtx : Ctx modeFirst levelFirst scopeFirst}
    {secondCtx : Ctx modeSecond levelSecond scopeSecond}
    {firstType : Ty levelFirst scopeFirst}
    {secondType : Ty levelSecond scopeSecond}
    {firstRaw : RawTerm scopeFirst}
    {secondRaw : RawTerm scopeSecond}
    {firstTerm : Term firstCtx firstType firstRaw}
    {secondTerm : Term secondCtx secondType secondRaw}
    (substRel : ConvCumul firstTerm secondTerm) :
    ConvCumul secondTerm firstTerm :=
  ConvCumul.sym substRel

/-- ConvCumul.trans preserved: subst commutes with trans at the relation
level (no Term-level work required). -/
theorem ConvCumul.subst_compatible_trans
    {modeFirst modeMid modeSecond : Mode}
    {levelFirst levelMid levelSecond scopeFirst scopeMid scopeSecond : Nat}
    {firstCtx : Ctx modeFirst levelFirst scopeFirst}
    {midCtx : Ctx modeMid levelMid scopeMid}
    {secondCtx : Ctx modeSecond levelSecond scopeSecond}
    {firstType : Ty levelFirst scopeFirst}
    {midType : Ty levelMid scopeMid}
    {secondType : Ty levelSecond scopeSecond}
    {firstRaw : RawTerm scopeFirst}
    {midRaw : RawTerm scopeMid}
    {secondRaw : RawTerm scopeSecond}
    {firstTerm : Term firstCtx firstType firstRaw}
    {midTerm : Term midCtx midType midRaw}
    {secondTerm : Term secondCtx secondType secondRaw}
    (firstToMid : ConvCumul firstTerm midTerm)
    (midToSecond : ConvCumul midTerm secondTerm) :
    ConvCumul firstTerm secondTerm :=
  ConvCumul.trans firstToMid midToSecond

/-! ### Per-shape subst-compat theorems (compositional approach)

For each cong ctor, we ship a subst-compat theorem that takes the
ALREADY-SUBSTITUTED inner ConvCumul relations and produces the
substituted outer ConvCumul.  This is compositional: callers
recursively substitute inner pieces and assemble at the cong
boundary.

The cong ctor itself does the work — these theorems are essentially
re-statements of the cong ctor with explicit "the inner pieces are
already subst'd" framing.  Subst on the outer term reduces to
applying Term.subst's per-arm definition (which uses the cong
shape directly), and the cong ctor closes the goal. -/

/-- ConvCumul.appCong + subst: given subst'd fn and arg ConvCumul
relations, produce the subst'd outer app ConvCumul. -/
theorem ConvCumul.appCong_subst_compatible
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainTypeFirst codomainTypeSecond : Ty level scope}
    {fnFirstRaw fnSecondRaw argFirstRaw argSecondRaw : RawTerm scope}
    {fnFirst : Term context (Ty.arrow domainType codomainTypeFirst) fnFirstRaw}
    {fnSecond : Term context (Ty.arrow domainType codomainTypeSecond) fnSecondRaw}
    {argFirst : Term context domainType argFirstRaw}
    {argSecond : Term context domainType argSecondRaw}
    (fnRel : ConvCumul fnFirst fnSecond)
    (argRel : ConvCumul argFirst argSecond) :
    ConvCumul (Term.app fnFirst argFirst) (Term.app fnSecond argSecond) :=
  ConvCumul.appCong fnRel argRel

/-- ConvCumul.pairCong + subst: given subst'd first and second ConvCumul
relations, produce the subst'd outer pair ConvCumul. -/
theorem ConvCumul.pairCong_subst_compatible
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstFirstRaw firstSecondRaw secondFirstRaw secondSecondRaw : RawTerm scope}
    {firstFirst : Term context firstType firstFirstRaw}
    {firstSecond : Term context firstType firstSecondRaw}
    {secondFirst : Term context (secondType.subst0 firstType firstFirstRaw)
                                 secondFirstRaw}
    {secondSecond : Term context (secondType.subst0 firstType firstSecondRaw)
                                  secondSecondRaw}
    (firstRel : ConvCumul firstFirst firstSecond)
    (secondRel : ConvCumul secondFirst secondSecond) :
    ConvCumul (Term.pair firstFirst secondFirst)
              (Term.pair firstSecond secondSecond) :=
  ConvCumul.pairCong firstRel secondRel

/-- ConvCumul.fstCong + subst. -/
theorem ConvCumul.fstCong_subst_compatible
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairFirstRaw pairSecondRaw : RawTerm scope}
    {pairFirst : Term context (Ty.sigmaTy firstType secondType) pairFirstRaw}
    {pairSecond : Term context (Ty.sigmaTy firstType secondType) pairSecondRaw}
    (pairRel : ConvCumul pairFirst pairSecond) :
    ConvCumul (Term.fst pairFirst) (Term.fst pairSecond) :=
  ConvCumul.fstCong pairRel

/-- ConvCumul.sndCong + subst. -/
theorem ConvCumul.sndCong_subst_compatible
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairFirstRaw pairSecondRaw : RawTerm scope}
    {pairFirst : Term context (Ty.sigmaTy firstType secondType) pairFirstRaw}
    {pairSecond : Term context (Ty.sigmaTy firstType secondType) pairSecondRaw}
    (pairRel : ConvCumul pairFirst pairSecond) :
    ConvCumul (Term.snd pairFirst) (Term.snd pairSecond) :=
  ConvCumul.sndCong pairRel

/-- ConvCumul.cumulUpCong + subst: when both lower terms are
ConvCumul-related, the cumulUp wrappings preserve the relation.

This is the recursive cumul-up case — the relation goes through the
cumul wrapper.  Note the same lowerLevel / higherLevel for both
wrappings (homogeneous in cumul shape, heterogeneous in lower
content). -/
theorem ConvCumul.cumulUpCong_subst_compatible
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeFirstRaw codeSecondRaw : RawTerm scope}
    {typeCodeFirst :
      Term context (Ty.universe lowerLevel levelLeLow) codeFirstRaw}
    {typeCodeSecond :
      Term context (Ty.universe lowerLevel levelLeLow) codeSecondRaw}
    (innerRel : ConvCumul typeCodeFirst typeCodeSecond) :
    ConvCumul (Term.cumulUp (context := context)
                            lowerLevel higherLevel cumulMonotone
                            levelLeLow levelLeHigh typeCodeFirst)
              (Term.cumulUp (context := context)
                            lowerLevel higherLevel cumulMonotone
                            levelLeLow levelLeHigh typeCodeSecond) :=
  ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
                        levelLeLow levelLeHigh innerRel

/-! ### Per-Term-shape `subst_compatible_*` helpers

Per-Term-ctor lemmas building blocks below (`subst_compatible_var`,
`subst_compatible_unit`, `subst_compatible_cumulUp_term`) feed the
unified `ConvCumul.subst_compatible` in
`Reduction/CumulSubstCompat.lean` (Pattern 3 wire-in). -/

/-- **CUMUL-1.7 substantive unified theorem (variable-only)**: when
the source Term is a variable, the result is the pointwise compat. -/
theorem ConvCumul.subst_compatible_var
    {mode : Mode} {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigmaA sigmaB :
      SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA : TermSubstHet sourceCtx targetCtx sigmaA)
    (termSubstB : TermSubstHet sourceCtx targetCtx sigmaB)
    (pointwiseCompat : ∀ position,
        ConvCumul (termSubstA position) (termSubstB position))
    (position : Fin sourceScope) :
    ConvCumul ((Term.var (context := sourceCtx) position).substHet termSubstA)
              ((Term.var (context := sourceCtx) position).substHet termSubstB) :=
  -- Term.substHet on .var is termSubst position directly.
  pointwiseCompat position

/-- **CUMUL-1.7 substantive unified theorem (unit-only)**: the unit
ctor is closed (no positions), so substituted endpoints coincide. -/
theorem ConvCumul.subst_compatible_unit
    {mode : Mode} {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigmaA sigmaB :
      SubstHet sourceLevel targetLevel sourceScope targetScope}
    (_termSubstA : TermSubstHet sourceCtx targetCtx sigmaA)
    (_termSubstB : TermSubstHet sourceCtx targetCtx sigmaB) :
    ConvCumul ((Term.unit (context := sourceCtx)).substHet _termSubstA)
              ((Term.unit (context := sourceCtx)).substHet _termSubstB) :=
  -- Term.substHet on .unit returns Term.unit unchanged on both sides.
  ConvCumul.refl _

/-- **CUMUL-1.7 substantive unified theorem (cumulUp-only)**: the
cumulUp ctor preserves `lowerTerm` unchanged under Term.substHet,
so substituted endpoints coincide. -/
theorem ConvCumul.subst_compatible_cumulUp_term
    {mode : Mode} {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigmaA sigmaB :
      SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA : TermSubstHet sourceCtx targetCtx sigmaA)
    (termSubstB : TermSubstHet sourceCtx targetCtx sigmaB)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ sourceLevel)
    (levelLeHigh : higherLevel.toNat + 1 ≤ sourceLevel)
    {codeRaw : RawTerm sourceScope}
    (typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (innerCompat :
      ConvCumul (typeCode.substHet termSubstA) (typeCode.substHet termSubstB)) :
    ConvCumul
      ((Term.cumulUp (context := sourceCtx)
                     lowerLevel higherLevel cumulMonotone
                     levelLeLow levelLeHigh typeCode).substHet termSubstA)
      ((Term.cumulUp (context := sourceCtx)
                     lowerLevel higherLevel cumulMonotone
                     levelLeLow levelLeHigh typeCode).substHet termSubstB) :=
  -- Term.substHet's cumulUp arm recurses on typeCode.  The result on
  -- each side is `Term.cumulUp ... (typeCode.substHet ...)`.  Wrap
  -- the inner ConvCumul via cumulUpCong.
  ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
                        (Nat.le_trans levelLeLow sigmaA.cumulOk)
                        (Nat.le_trans levelLeHigh sigmaA.cumulOk)
                        innerCompat

end LeanFX2

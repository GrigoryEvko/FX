import LeanFX2.Reduction.Cumul

/-! # LeanFX2.Reduction.ConvCumulHomo.Relation

Defines the homogeneous-context-only inductive `ConvCumulHomo`, a
sister inductive to `ConvCumul` (in `Reduction/Cumul.lean`) that
EXCLUDES the cross-context `viaUp` constructor.  Includes 26 ctors:
refl + sym + trans + 22 cong rules + cumulUpCong (homogeneous in
outer ctx).  ConvCumul has 27 ctors total — the ONE excluded is viaUp.

`viaUp` is the cross-context cumul-promotion ctor.  Its endpoints are
HETEROGENEOUS in scope/level/ctx, so a unified single-`σ` substitution
theorem is genuinely ill-typed for viaUp — a single σ at outer scope
cannot rename `lowerTerm` at `scopeLow`.

Lean 4.29.1's dep-pattern matcher cannot unify viaUp's heterogeneous
indices when the outer relation is constrained to homogeneous context.
`ConvCumulHomo` sidesteps this wall by construction.

## Root status

Layer 3 conv-cumul homogeneous helper.  Pure inductive declaration —
no theorems shipped from this file. -/

namespace LeanFX2


/-- Homogeneous-context-only ConvCumul.  All ctors mirror `ConvCumul`
EXCEPT `viaUp` (which is the only cross-context ctor).  Indices on
both endpoints share `mode` / `level` / `scope` / `ctx`. -/
inductive ConvCumulHomo : ∀ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope},
    Term context firstType firstRaw →
    Term context secondType secondRaw → Prop
  /-- Reflexivity. -/
  | refl
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {someType : Ty level scope} {someRaw : RawTerm scope}
      (someTerm : Term context someType someRaw) :
      ConvCumulHomo someTerm someTerm
  /-- Symmetry. -/
  | sym
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType secondType : Ty level scope}
      {firstRaw secondRaw : RawTerm scope}
      {firstTerm : Term context firstType firstRaw}
      {secondTerm : Term context secondType secondRaw}
      (rel : ConvCumulHomo firstTerm secondTerm) :
      ConvCumulHomo secondTerm firstTerm
  /-- Transitivity (homogeneous: mid lives in same context). -/
  | trans
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType midType secondType : Ty level scope}
      {firstRaw midRaw secondRaw : RawTerm scope}
      {firstTerm : Term context firstType firstRaw}
      {midTerm : Term context midType midRaw}
      {secondTerm : Term context secondType secondRaw}
      (firstToMid : ConvCumulHomo firstTerm midTerm)
      (midToSecond : ConvCumulHomo midTerm secondTerm) :
      ConvCumulHomo firstTerm secondTerm
  -- Cong ctors (all 19 — same as ConvCumul minus viaUp)
  | lamCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainTypeFirst codomainTypeSecond : Ty level scope}
      {bodyFirstRaw bodySecondRaw : RawTerm (scope + 1)}
      {bodyFirst : Term (Ctx.cons context domainType)
                          codomainTypeFirst.weaken bodyFirstRaw}
      {bodySecond : Term (Ctx.cons context domainType)
                           codomainTypeSecond.weaken bodySecondRaw}
      (bodyRel : ConvCumulHomo bodyFirst bodySecond) :
      ConvCumulHomo (Term.lam bodyFirst) (Term.lam bodySecond)
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
      (bodyRel : ConvCumulHomo bodyFirst bodySecond) :
      ConvCumulHomo (Term.lamPi bodyFirst) (Term.lamPi bodySecond)
  | appCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainTypeFirst codomainTypeSecond : Ty level scope}
      {fnFirstRaw fnSecondRaw argFirstRaw argSecondRaw : RawTerm scope}
      {fnFirst : Term context (Ty.arrow domainType codomainTypeFirst) fnFirstRaw}
      {fnSecond : Term context (Ty.arrow domainType codomainTypeSecond) fnSecondRaw}
      {argFirst : Term context domainType argFirstRaw}
      {argSecond : Term context domainType argSecondRaw}
      (fnRel : ConvCumulHomo fnFirst fnSecond)
      (argRel : ConvCumulHomo argFirst argSecond) :
      ConvCumulHomo (Term.app fnFirst argFirst) (Term.app fnSecond argSecond)
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
      (fnRel : ConvCumulHomo fnFirst fnSecond)
      (argRel : ConvCumulHomo argFirst argSecond) :
      ConvCumulHomo (Term.appPi fnFirst argFirst) (Term.appPi fnSecond argSecond)
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
      (firstRel : ConvCumulHomo firstFirst firstSecond)
      (secondRel : ConvCumulHomo secondFirst secondSecond) :
      ConvCumulHomo (Term.pair firstFirst secondFirst)
                    (Term.pair firstSecond secondSecond)
  | fstCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {pairFirstRaw pairSecondRaw : RawTerm scope}
      {pairFirst : Term context (Ty.sigmaTy firstType secondType) pairFirstRaw}
      {pairSecond : Term context (Ty.sigmaTy firstType secondType) pairSecondRaw}
      (pairRel : ConvCumulHomo pairFirst pairSecond) :
      ConvCumulHomo (Term.fst pairFirst) (Term.fst pairSecond)
  | sndCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType : Ty level scope}
      {secondType : Ty level (scope + 1)}
      {pairFirstRaw pairSecondRaw : RawTerm scope}
      {pairFirst : Term context (Ty.sigmaTy firstType secondType) pairFirstRaw}
      {pairSecond : Term context (Ty.sigmaTy firstType secondType) pairSecondRaw}
      (pairRel : ConvCumulHomo pairFirst pairSecond) :
      ConvCumulHomo (Term.snd pairFirst) (Term.snd pairSecond)
  | boolElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {thenFirstRaw thenSecondRaw elseFirstRaw elseSecondRaw : RawTerm scope}
      {scrutFirst : Term context Ty.bool scrutFirstRaw}
      {scrutSecond : Term context Ty.bool scrutSecondRaw}
      {thenFirst :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenFirstRaw}
      {thenSecond :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenSecondRaw}
      {elseFirst :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseFirstRaw}
      {elseSecond :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseSecondRaw}
      (scrutRel : ConvCumulHomo scrutFirst scrutSecond)
      (thenRel : ConvCumulHomo thenFirst thenSecond)
      (elseRel : ConvCumulHomo elseFirst elseSecond) :
      ConvCumulHomo (Term.boolElim scrutFirst thenFirst elseFirst)
                    (Term.boolElim scrutSecond thenSecond elseSecond)
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
      (scrutRel : ConvCumulHomo scrutFirst scrutSecond)
      (zeroRel : ConvCumulHomo zeroFirst zeroSecond)
      (succRel : ConvCumulHomo succFirst succSecond) :
      ConvCumulHomo (Term.natElim scrutFirst zeroFirst succFirst)
                    (Term.natElim scrutSecond zeroSecond succSecond)
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
      (scrutRel : ConvCumulHomo scrutFirst scrutSecond)
      (zeroRel : ConvCumulHomo zeroFirst zeroSecond)
      (succRel : ConvCumulHomo succFirst succSecond) :
      ConvCumulHomo (Term.natRec scrutFirst zeroFirst succFirst)
                    (Term.natRec scrutSecond zeroSecond succSecond)
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
      (scrutRel : ConvCumulHomo scrutFirst scrutSecond)
      (nilRel : ConvCumulHomo nilFirst nilSecond)
      (consRel : ConvCumulHomo consFirst consSecond) :
      ConvCumulHomo (Term.listElim scrutFirst nilFirst consFirst)
                    (Term.listElim scrutSecond nilSecond consSecond)
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
      (scrutRel : ConvCumulHomo scrutFirst scrutSecond)
      (noneRel : ConvCumulHomo noneFirst noneSecond)
      (someRel : ConvCumulHomo someFirst someSecond) :
      ConvCumulHomo (Term.optionMatch scrutFirst noneFirst someFirst)
                    (Term.optionMatch scrutSecond noneSecond someSecond)
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
      (scrutRel : ConvCumulHomo scrutFirst scrutSecond)
      (leftRel : ConvCumulHomo leftFirst leftSecond)
      (rightRel : ConvCumulHomo rightFirst rightSecond) :
      ConvCumulHomo (Term.eitherMatch scrutFirst leftFirst rightFirst)
                    (Term.eitherMatch scrutSecond leftSecond rightSecond)
  | natSuccCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {predFirstRaw predSecondRaw : RawTerm scope}
      {predFirst : Term context Ty.nat predFirstRaw}
      {predSecond : Term context Ty.nat predSecondRaw}
      (predRel : ConvCumulHomo predFirst predSecond) :
      ConvCumulHomo (Term.natSucc predFirst) (Term.natSucc predSecond)
  | listConsCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headFirstRaw headSecondRaw tailFirstRaw tailSecondRaw : RawTerm scope}
      {headFirst : Term context elementType headFirstRaw}
      {headSecond : Term context elementType headSecondRaw}
      {tailFirst : Term context (Ty.listType elementType) tailFirstRaw}
      {tailSecond : Term context (Ty.listType elementType) tailSecondRaw}
      (headRel : ConvCumulHomo headFirst headSecond)
      (tailRel : ConvCumulHomo tailFirst tailSecond) :
      ConvCumulHomo (Term.listCons headFirst tailFirst)
                    (Term.listCons headSecond tailSecond)
  | optionSomeCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {valueFirstRaw valueSecondRaw : RawTerm scope}
      {valueFirst : Term context elementType valueFirstRaw}
      {valueSecond : Term context elementType valueSecondRaw}
      (valueRel : ConvCumulHomo valueFirst valueSecond) :
      ConvCumulHomo (Term.optionSome valueFirst) (Term.optionSome valueSecond)
  | eitherInlCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueFirstRaw valueSecondRaw : RawTerm scope}
      {valueFirst : Term context leftType valueFirstRaw}
      {valueSecond : Term context leftType valueSecondRaw}
      (valueRel : ConvCumulHomo valueFirst valueSecond) :
      ConvCumulHomo (Term.eitherInl (rightType := rightType) valueFirst)
                    (Term.eitherInl (rightType := rightType) valueSecond)
  | eitherInrCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueFirstRaw valueSecondRaw : RawTerm scope}
      {valueFirst : Term context rightType valueFirstRaw}
      {valueSecond : Term context rightType valueSecondRaw}
      (valueRel : ConvCumulHomo valueFirst valueSecond) :
      ConvCumulHomo (Term.eitherInr (leftType := leftType) valueFirst)
                    (Term.eitherInr (leftType := leftType) valueSecond)
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
      (baseRel : ConvCumulHomo baseFirst baseSecond)
      (witnessRel : ConvCumulHomo witnessFirst witnessSecond) :
      ConvCumulHomo (Term.idJ baseFirst witnessFirst)
                    (Term.idJ baseSecond witnessSecond)
  | modIntroCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context innerType innerFirstRaw}
      {innerSecond : Term context innerType innerSecondRaw}
      (innerRel : ConvCumulHomo innerFirst innerSecond) :
      ConvCumulHomo (Term.modIntro innerFirst) (Term.modIntro innerSecond)
  | modElimCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context innerType innerFirstRaw}
      {innerSecond : Term context innerType innerSecondRaw}
      (innerRel : ConvCumulHomo innerFirst innerSecond) :
      ConvCumulHomo (Term.modElim innerFirst) (Term.modElim innerSecond)
  | subsumeCong
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerFirstRaw innerSecondRaw : RawTerm scope}
      {innerFirst : Term context innerType innerFirstRaw}
      {innerSecond : Term context innerType innerSecondRaw}
      (innerRel : ConvCumulHomo innerFirst innerSecond) :
      ConvCumulHomo (Term.subsume innerFirst) (Term.subsume innerSecond)
  /-- Cross-level cumul promotion's cong rule.  The inner `lowerRel`
  is at decoupled `scopeLow` (independent of outer scope), and takes
  the FULL `ConvCumul` (not ConvCumulHomo) — the lower side may
  itself contain viaUp witnesses, totally separate from the outer
  homogeneous structure.  Outer ctx is HOMOGENEOUS (both sides at
  same `ctxHigh`), so this ctor fits ConvCumulHomo's discipline
  even though the inner lowerRel is full ConvCumul. -/
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
      (innerHomoRel : ConvCumulHomo typeCodeFirst typeCodeSecond) :
      ConvCumulHomo
        (Term.cumulUp (context := context)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCodeFirst)
        (Term.cumulUp (context := context)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCodeSecond)


end LeanFX2

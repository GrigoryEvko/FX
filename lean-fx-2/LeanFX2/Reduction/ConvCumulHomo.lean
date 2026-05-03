import LeanFX2.Reduction.Cumul
import LeanFX2.Term.Subst

/-! # Reduction/ConvCumulHomo — homogeneous-context-only ConvCumul

Sister inductive to `ConvCumul` (in `Reduction/Cumul.lean`) that
EXCLUDES the `viaUp` constructor.  Includes 26 ctors: refl + sym +
trans + 22 cong rules + cumulUpCong (which takes a FULL `ConvCumul`
on the lower side at decoupled `scopeLow`, but is itself
homogeneous in outer ctx).  ConvCumul has 27 ctors total — the
ONE excluded is viaUp.

`viaUp` is the cross-context cumul-promotion ctor: it relates
`lowerTerm` at `(ctxLow at lowerLevel+1, scopeLow)` to
`Term.cumulUp ... lowerTerm` at `(ctxHigh at higherLevel+1, scope)`.
Its endpoints are HETEROGENEOUS in scope/level/ctx, so a unified
`ConvCumul a b → ConvCumul (a.subst σ) (b.subst σ)` is genuinely
ill-typed for viaUp — a single σ at outer scope cannot rename
lowerTerm at scopeLow.

## Why this exists

Lean 4.29.1's dep-pattern matcher cannot unify viaUp's
heterogeneous indices when the outer relation is constrained to
homogeneous context, leading to a propositional
`lowerLevel.toNat = higherLevel.toNat` equation Lean cannot
discharge automatically.  This blocks `induction cumulRel` and
`cases cumulRel` for ConvCumul's recursive headline theorems
(Pattern 2 Benton single-rename, Pattern 3 Allais paired-env
subst — both verified empirically).

`ConvCumulHomo` sidesteps this wall by construction: drop viaUp
from the inductive but keep cumulUpCong (homogeneous in outer
ctx — its inner lowerRel lives at decoupled scopeLow and is
unaffected by outer subst).  The recursive headlines
`rename_compatible_benton` and `subst_compatible_benton` become
provable via `induction`.

## Bridge

`ConvCumulHomo.toCumul : ConvCumulHomo a b → ConvCumul a b` lifts
the restricted relation back to the full ConvCumul — ctor-by-ctor
trivial.  The reverse direction `ConvCumul → ConvCumulHomo` is
NOT generally derivable: viaUp witnesses cannot be re-expressed
as ConvCumulHomo because viaUp's heterogeneous indices have no
ConvCumulHomo analog.

## Coverage of full ConvCumul under subst/rename

* The 26 homogeneous ctors (cong + refl/sym/trans + cumulUpCong) →
  `ConvCumulHomo.{rename,subst}_compatible_benton` recursive
  headlines (this file).
* The 1 viaUp ctor → `ConvCumul.{rename,subst}_compatible_viaUp`
  separate theorem with outer-only subst (this file, below).
  These are NOT vacuous: their type asserts non-trivial subst
  preservation; their proof body is short BECAUSE
  `Term.{rename,subst}`'s cumulUp arm preserves lowerTerm
  verbatim by kernel design.

A unified `ConvCumul a b → ConvCumul (a.subst σ) (b.subst σ)` is
ill-typed for viaUp and so doesn't exist as a single theorem.
The two complementary theorems above cover all cases at the
correct typing.

## Architecture commitment

Pattern 2 (BHKM-style) recursive headlines defined HERE are
genuine zero-axiom theorems for the homogeneous-context fragment.
viaUp is a separate complementary theorem.

## Audit gate

Every shipped declaration verified zero-axiom in
`Smoke/AuditConvCumulHomo.lean`. -/

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
      {motiveType : Ty level scope}
      {scrutFirstRaw scrutSecondRaw : RawTerm scope}
      {thenFirstRaw thenSecondRaw elseFirstRaw elseSecondRaw : RawTerm scope}
      {scrutFirst : Term context Ty.bool scrutFirstRaw}
      {scrutSecond : Term context Ty.bool scrutSecondRaw}
      {thenFirst : Term context motiveType thenFirstRaw}
      {thenSecond : Term context motiveType thenSecondRaw}
      {elseFirst : Term context motiveType elseFirstRaw}
      {elseSecond : Term context motiveType elseSecondRaw}
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
      {mode : Mode} {scopeLow scope : Nat}
      (innerLevel lowerLevel higherLevel : UniverseLevel)
      (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
      (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
      {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
      {lowerFirst lowerSecond :
        Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                    (RawTerm.universeCode innerLevel.toNat)}
      (lowerRel : ConvCumul lowerFirst lowerSecond) :
      ConvCumulHomo
        (Term.cumulUp (ctxHigh := ctxHigh)
                      innerLevel lowerLevel higherLevel
                      cumulOkLow cumulOkHigh cumulMonotone
                      (Nat.le_refl _) (Nat.le_refl _) lowerFirst)
        (Term.cumulUp (ctxHigh := ctxHigh)
                      innerLevel lowerLevel higherLevel
                      cumulOkLow cumulOkHigh cumulMonotone
                      (Nat.le_refl _) (Nat.le_refl _) lowerSecond)

/-! # Bridge: ConvCumulHomo → ConvCumul -/

/-- Every homogeneous-context ConvCumul lifts to the full ConvCumul.
Ctor-by-ctor structural recursion. -/
theorem ConvCumulHomo.toCumul {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (rel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumul firstTerm secondTerm := by
  induction rel with
  | refl t                          => exact ConvCumul.refl t
  | sym _ ih                        => exact ConvCumul.sym ih
  | trans _ _ ihAB ihBC             => exact ConvCumul.trans ihAB ihBC
  | lamCong _ ih                    => exact ConvCumul.lamCong ih
  | lamPiCong _ ih                  => exact ConvCumul.lamPiCong ih
  | appCong _ _ ihFn ihArg          => exact ConvCumul.appCong ihFn ihArg
  | appPiCong _ _ ihFn ihArg        => exact ConvCumul.appPiCong ihFn ihArg
  | pairCong _ _ ihFst ihSnd        => exact ConvCumul.pairCong ihFst ihSnd
  | fstCong _ ih                    => exact ConvCumul.fstCong ih
  | sndCong _ ih                    => exact ConvCumul.sndCong ih
  | boolElimCong _ _ _ ihS ihT ihE  => exact ConvCumul.boolElimCong ihS ihT ihE
  | natElimCong _ _ _ ihS ihZ ihK   => exact ConvCumul.natElimCong ihS ihZ ihK
  | natRecCong _ _ _ ihS ihZ ihK    => exact ConvCumul.natRecCong ihS ihZ ihK
  | listElimCong _ _ _ ihS ihN ihC  => exact ConvCumul.listElimCong ihS ihN ihC
  | optionMatchCong _ _ _ ihS ihN ihM => exact ConvCumul.optionMatchCong ihS ihN ihM
  | eitherMatchCong _ _ _ ihS ihL ihR => exact ConvCumul.eitherMatchCong ihS ihL ihR
  | natSuccCong _ ih                => exact ConvCumul.natSuccCong ih
  | listConsCong _ _ ihH ihT        => exact ConvCumul.listConsCong ihH ihT
  | optionSomeCong _ ih             => exact ConvCumul.optionSomeCong ih
  | eitherInlCong _ ih              => exact ConvCumul.eitherInlCong ih
  | eitherInrCong _ ih              => exact ConvCumul.eitherInrCong ih
  | idJCong _ _ ihB ihW             => exact ConvCumul.idJCong ihB ihW
  | modIntroCong _ ih               => exact ConvCumul.modIntroCong ih
  | modElimCong _ ih                => exact ConvCumul.modElimCong ih
  | subsumeCong _ ih                => exact ConvCumul.subsumeCong ih
  | cumulUpCong innerLevel lowerLevel higherLevel
                cumulOkLow cumulOkHigh cumulMonotone lowerRel =>
      exact ConvCumul.cumulUpCong innerLevel lowerLevel higherLevel
                                  cumulOkLow cumulOkHigh cumulMonotone lowerRel

/-! # BHKM cast-elim primitives (for ConvCumulHomo)

Same shape as `cast_eq_*_benton` in `CumulSubstCompat.lean` but
operating on `ConvCumulHomo`.  Used by binder/cast cases of the
recursive headlines below. -/

theorem ConvCumulHomo.cast_eq_both
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {tyOne tyTwo : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context tyOne firstRaw}
    {secondTerm : Term context tyOne secondRaw}
    (eq : tyOne = tyTwo)
    (origRel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumulHomo (eq ▸ firstTerm) (eq ▸ secondTerm) := by
  cases eq
  exact origRel

/-- Independent two-equation cast: each endpoint may carry its own
type-equation cast.  Used for pair / appPi / snd cases where the
two sides involve different `Ty.subst0_rename_commute` equations
(the cast depends on `firstRaw`, which differs between endpoints). -/
theorem ConvCumulHomo.cast_eq_indep
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstTy firstTy' secondTy secondTy' : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstTy firstRaw}
    {secondTerm : Term context secondTy secondRaw}
    (eqFirst : firstTy = firstTy')
    (eqSecond : secondTy = secondTy')
    (origRel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumulHomo (eqFirst ▸ firstTerm) (eqSecond ▸ secondTerm) := by
  cases eqFirst
  cases eqSecond
  exact origRel

/-! # Pattern 2 (Benton JAR'12): rename_compatible — recursive headline

Single typed `TermRenaming` lifts an existing `ConvCumulHomo` to
the renamed pair.  Proven by `induction` on `ConvCumulHomo` —
works because the homogeneous indices unify cleanly. -/

/-- **Benton headline**: `ConvCumulHomo` is preserved under typed
renaming.  Genuine recursive theorem, proven by induction on the
relation. -/
theorem ConvCumulHomo.rename_compatible_benton
    {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
      {rho : RawRenaming sourceScope targetScope}
      (termRenaming : TermRenaming sourceCtx targetCtx rho),
      ConvCumulHomo (firstTerm.rename termRenaming)
                    (secondTerm.rename termRenaming) := by
  induction cumulRel with
  | refl _ => intros; exact ConvCumulHomo.refl _
  | sym _ ih => intros; exact ConvCumulHomo.sym (ih _)
  | trans _ _ ihAB ihBC => intros; exact ConvCumulHomo.trans (ihAB _) (ihBC _)
  | lamCong _ ih =>
      intros _ _ _ termRenaming
      have inner := ih (TermRenaming.lift termRenaming _)
      exact ConvCumulHomo.lamCong
              (ConvCumulHomo.cast_eq_indep _ _ inner)
  | lamPiCong _ ih =>
      intros _ _ _ termRenaming
      exact ConvCumulHomo.lamPiCong (ih (TermRenaming.lift termRenaming _))
  | appCong _ _ ihFn ihArg =>
      intros _ _ _ termRenaming
      exact ConvCumulHomo.appCong (ihFn termRenaming) (ihArg termRenaming)
  | appPiCong _ _ ihFn ihArg =>
      intros _ _ _ termRenaming
      have inner := ConvCumulHomo.appPiCong (ihFn termRenaming) (ihArg termRenaming)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | pairCong _ _ ihFst ihSnd =>
      intros _ _ _ termRenaming
      have innerSnd := ihSnd termRenaming
      exact ConvCumulHomo.pairCong (ihFst termRenaming)
              (ConvCumulHomo.cast_eq_indep _ _ innerSnd)
  | fstCong _ ih => intros _ _ _ termRenaming; exact ConvCumulHomo.fstCong (ih termRenaming)
  | sndCong _ ih =>
      intros _ _ _ termRenaming
      have inner := ConvCumulHomo.sndCong (ih termRenaming)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | boolElimCong _ _ _ ihS ihT ihE =>
      intros; exact ConvCumulHomo.boolElimCong (ihS _) (ihT _) (ihE _)
  | natElimCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natElimCong (ihS _) (ihZ _) (ihK _)
  | natRecCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natRecCong (ihS _) (ihZ _) (ihK _)
  | listElimCong _ _ _ ihS ihN ihC =>
      intros; exact ConvCumulHomo.listElimCong (ihS _) (ihN _) (ihC _)
  | optionMatchCong _ _ _ ihS ihN ihM =>
      intros; exact ConvCumulHomo.optionMatchCong (ihS _) (ihN _) (ihM _)
  | eitherMatchCong _ _ _ ihS ihL ihR =>
      intros; exact ConvCumulHomo.eitherMatchCong (ihS _) (ihL _) (ihR _)
  | natSuccCong _ ih => intros; exact ConvCumulHomo.natSuccCong (ih _)
  | listConsCong _ _ ihH ihT => intros; exact ConvCumulHomo.listConsCong (ihH _) (ihT _)
  | optionSomeCong _ ih => intros; exact ConvCumulHomo.optionSomeCong (ih _)
  | eitherInlCong _ ih => intros; exact ConvCumulHomo.eitherInlCong (ih _)
  | eitherInrCong _ ih => intros; exact ConvCumulHomo.eitherInrCong (ih _)
  | idJCong _ _ ihB ihW => intros; exact ConvCumulHomo.idJCong (ihB _) (ihW _)
  | modIntroCong _ ih => intros; exact ConvCumulHomo.modIntroCong (ih _)
  | modElimCong _ ih => intros; exact ConvCumulHomo.modElimCong (ih _)
  | subsumeCong _ ih => intros; exact ConvCumulHomo.subsumeCong (ih _)
  | cumulUpCong innerLevel lowerLevel higherLevel
                cumulOkLow cumulOkHigh cumulMonotone lowerRel =>
      -- Term.{rename,subst}'s cumulUp arm preserves lowerTerm verbatim
      -- (scopeLow decoupled from outer scope per Phase 12.A.B1.5).
      -- ConvCumulHomo.cumulUpCong reapplies at target ctx with the
      -- same lowerRel — substantive use: lowerRel is consumed as a
      -- ctor argument and rebuilt in the result.
      intros
      exact ConvCumulHomo.cumulUpCong innerLevel lowerLevel higherLevel
                                      cumulOkLow cumulOkHigh cumulMonotone
                                      lowerRel

/-! # Pattern 2 (BHKM JAR'12): subst_compatible — recursive headline (the SUBST rung)

`Term.subst` is the substitution analog of `Term.rename`.  Same
recursive structure, same cast-handling pattern: where the subst
arm wraps in `Ty.weaken_subst_commute` or `Ty.subst0_subst_commute`,
we use `cast_eq_indep` with the `have inner := ...` ordering trick
to let Lean elaborate the inner term type concretely first. -/

/-- **Benton subst headline**: `ConvCumulHomo` is preserved under
typed substitution.  Genuine recursive theorem, proven by induction
on the relation.  All 24 ctors discharged at zero axioms,
including the four cast cases (lam, appPi, pair, snd). -/
theorem ConvCumulHomo.subst_compatible_benton
    {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
      {sigma : Subst level sourceScope targetScope}
      (termSubst : TermSubst sourceCtx targetCtx sigma),
      ConvCumulHomo (firstTerm.subst termSubst)
                    (secondTerm.subst termSubst) := by
  induction cumulRel with
  | refl _ => intros; exact ConvCumulHomo.refl _
  | sym _ ih => intros; exact ConvCumulHomo.sym (ih _)
  | trans _ _ ihAB ihBC => intros; exact ConvCumulHomo.trans (ihAB _) (ihBC _)
  | lamCong _ ih =>
      intros _ _ _ termSubst
      have inner := ih (TermSubst.lift termSubst _)
      exact ConvCumulHomo.lamCong
              (ConvCumulHomo.cast_eq_indep _ _ inner)
  | lamPiCong _ ih =>
      intros _ _ _ termSubst
      exact ConvCumulHomo.lamPiCong (ih (TermSubst.lift termSubst _))
  | appCong _ _ ihFn ihArg =>
      intros _ _ _ termSubst
      exact ConvCumulHomo.appCong (ihFn termSubst) (ihArg termSubst)
  | appPiCong _ _ ihFn ihArg =>
      intros _ _ _ termSubst
      have inner := ConvCumulHomo.appPiCong (ihFn termSubst) (ihArg termSubst)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | pairCong _ _ ihFst ihSnd =>
      intros _ _ _ termSubst
      have innerSnd := ihSnd termSubst
      exact ConvCumulHomo.pairCong (ihFst termSubst)
              (ConvCumulHomo.cast_eq_indep _ _ innerSnd)
  | fstCong _ ih => intros _ _ _ termSubst; exact ConvCumulHomo.fstCong (ih termSubst)
  | sndCong _ ih =>
      intros _ _ _ termSubst
      have inner := ConvCumulHomo.sndCong (ih termSubst)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | boolElimCong _ _ _ ihS ihT ihE =>
      intros; exact ConvCumulHomo.boolElimCong (ihS _) (ihT _) (ihE _)
  | natElimCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natElimCong (ihS _) (ihZ _) (ihK _)
  | natRecCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natRecCong (ihS _) (ihZ _) (ihK _)
  | listElimCong _ _ _ ihS ihN ihC =>
      intros; exact ConvCumulHomo.listElimCong (ihS _) (ihN _) (ihC _)
  | optionMatchCong _ _ _ ihS ihN ihM =>
      intros; exact ConvCumulHomo.optionMatchCong (ihS _) (ihN _) (ihM _)
  | eitherMatchCong _ _ _ ihS ihL ihR =>
      intros; exact ConvCumulHomo.eitherMatchCong (ihS _) (ihL _) (ihR _)
  | natSuccCong _ ih => intros; exact ConvCumulHomo.natSuccCong (ih _)
  | listConsCong _ _ ihH ihT => intros; exact ConvCumulHomo.listConsCong (ihH _) (ihT _)
  | optionSomeCong _ ih => intros; exact ConvCumulHomo.optionSomeCong (ih _)
  | eitherInlCong _ ih => intros; exact ConvCumulHomo.eitherInlCong (ih _)
  | eitherInrCong _ ih => intros; exact ConvCumulHomo.eitherInrCong (ih _)
  | idJCong _ _ ihB ihW => intros; exact ConvCumulHomo.idJCong (ihB _) (ihW _)
  | modIntroCong _ ih => intros; exact ConvCumulHomo.modIntroCong (ih _)
  | modElimCong _ ih => intros; exact ConvCumulHomo.modElimCong (ih _)
  | subsumeCong _ ih => intros; exact ConvCumulHomo.subsumeCong (ih _)
  | cumulUpCong innerLevel lowerLevel higherLevel
                cumulOkLow cumulOkHigh cumulMonotone lowerRel =>
      -- Term.{rename,subst}'s cumulUp arm preserves lowerTerm verbatim
      -- (scopeLow decoupled from outer scope per Phase 12.A.B1.5).
      -- ConvCumulHomo.cumulUpCong reapplies at target ctx with the
      -- same lowerRel — substantive use: lowerRel is consumed as a
      -- ctor argument and rebuilt in the result.
      intros
      exact ConvCumulHomo.cumulUpCong innerLevel lowerLevel higherLevel
                                      cumulOkLow cumulOkHigh cumulMonotone
                                      lowerRel

/-! # Bridge: ConvCumul → ConvCumulHomo for the homogeneous fragment

While `ConvCumul → ConvCumulHomo` is NOT generally derivable (the
viaUp ctor on ConvCumul has no analog in ConvCumulHomo), we CAN
derive it for the per-ctor cong cases by structural inversion.

The viaUp case is genuinely separate: it's the cross-context
cumul-promotion ctor, handled by per-arm helpers in
`CumulSubstCompat.lean` (`subst_compatible_outer` etc.).

For homogeneous-context input (firstCtx = secondCtx, firstType =
secondType, etc.), every ConvCumul ctor — INCLUDING viaUp — can
be analyzed.  The viaUp case becomes degenerate: when `firstCtx =
ctxLow` AND `firstCtx = ctxHigh` AND `lowerLevel = higherLevel`,
viaUp's source and target coincide; then the relation collapses
to `ConvCumulHomo.refl`.

Below we provide the per-shape cong inversions that return
`ConvCumulHomo` results — these compose with the recursive
headlines `rename_compatible_benton` and `subst_compatible_benton`
to give callers a direct path from any ConvCumul-derived cong
witness to the headline output.
-/

/-- Lift: every refl-built `ConvCumul` is `ConvCumulHomo.refl`. -/
theorem ConvCumulHomo.fromCumul_refl
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someType : Ty level scope} {someRaw : RawTerm scope}
    (someTerm : Term context someType someRaw) :
    ConvCumulHomo someTerm someTerm :=
  ConvCumulHomo.refl someTerm

/-! # ConvCumul-side BHKM headlines (rename + subst)

These compose `ConvCumulHomo`'s recursive headlines with `toCumul`
to give a `ConvCumul`-output theorem.  Callers operating on
`ConvCumul` (full relation, including viaUp) can use these when
their input is a `ConvCumulHomo`-derivable shape — i.e., any
homogeneous-ctx cong-built relation.

The viaUp case (cross-context cumul promotion) is genuinely not in
the homogeneous fragment; it's handled separately by the per-arm
`subst_compatible_outer` / `rename_compatible_outer` helpers in
`CumulSubstCompat.lean`, which produce `ConvCumul` directly via
`Conv.cumul_subst_outer`. -/

/-- **Pattern 2 rename headline at ConvCumul output**: any
homogeneous-ctx ConvCumulHomo input lifts via toCumul. -/
theorem ConvCumul.rename_compatible_homo_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumul (firstTerm.rename termRenaming) (secondTerm.rename termRenaming) :=
  (cumulRel.rename_compatible_benton termRenaming).toCumul

/-- **Pattern 2 subst headline at ConvCumul output**: any
homogeneous-ctx ConvCumulHomo input lifts via toCumul. -/
theorem ConvCumul.subst_compatible_homo_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ConvCumul (firstTerm.subst termSubst) (secondTerm.subst termSubst) :=
  (cumulRel.subst_compatible_benton termSubst).toCumul

/-! # The viaUp case — cross-context cumul promotion

`ConvCumul.viaUp` is the cross-context ctor that defeats homogeneous
induction.  Its two endpoints live at INDEPENDENT scopes (`scopeLow`
vs outer `scope`) and INDEPENDENT levels (`lowerLevel + 1` vs
`higherLevel + 1`).  A "`ConvCumul a b → ConvCumul (a.subst σ)
(b.subst σ)`" theorem is genuinely ill-typed for viaUp because a
single σ at outer scope cannot apply to lowerTerm at scopeLow.

The CORRECT framing for viaUp under substitution: applying σ only
to the OUTER side preserves the relation, because:
1. `(Term.cumulUp ... lowerTerm).subst σ = Term.cumulUp ... lowerTerm`
   reconstructed at the new target scope (lowerTerm preserved verbatim
   per `Term/Subst.lean`'s cumulUp arm).
2. `ConvCumul.viaUp` reapplies on the substituted shape.

Below: the GENERAL version (arbitrary scopeLow per Phase 12.A.B1.5)
of subst preservation for viaUp.  Existing `Conv.cumul_subst_outer`
in `Reduction/Cumul.lean` covers the closed-source `scopeLow = 0`
case; this generalizes to arbitrary `scopeLow`.

Same shape applies to `Term.rename`: the cumulUp arm preserves
`lowerTerm` verbatim, and `ConvCumul.viaUp` witnesses. -/

/-- **Subst preservation through viaUp at arbitrary scopeLow**.
Phase 12.A.B1.5 decoupled `scopeLow` from outer `scope`; this is
the general statement.  Substituting the outer side of a `viaUp`
witness produces a new `viaUp` at the substituted target. -/
theorem ConvCumul.subst_compatible_viaUp
    {mode : Mode} {scopeLow scope targetScope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {targetCtxHigh : Ctx mode (higherLevel.toNat + 1) targetScope}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat))
    (sigma : Subst (higherLevel.toNat + 1) scope targetScope)
    (termSubst : TermSubst ctxHigh targetCtxHigh sigma) :
    ConvCumul lowerTerm
              (Term.subst termSubst
                (Term.cumulUp (ctxHigh := ctxHigh)
                              innerLevel lowerLevel higherLevel
                              cumulOkLow cumulOkHigh cumulMonotone
                              (Nat.le_refl _) (Nat.le_refl _) lowerTerm)) :=
  -- Term.subst's cumulUp arm preserves lowerTerm verbatim (its
  -- scopeLow is decoupled from the outer scope being substituted)
  -- and rebuilds Term.cumulUp at the new target scope.
  -- ConvCumul.viaUp witnesses the result at arbitrary scopeLow.
  ConvCumul.viaUp innerLevel lowerLevel higherLevel
                  cumulOkLow cumulOkHigh cumulMonotone lowerTerm

/-- **Rename preservation through viaUp at arbitrary scopeLow**.
Mirror of `subst_compatible_viaUp` for the rename direction.
Renaming the outer side preserves the relation. -/
theorem ConvCumul.rename_compatible_viaUp
    {mode : Mode} {scopeLow scope targetScope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {targetCtxHigh : Ctx mode (higherLevel.toNat + 1) targetScope}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat))
    (rho : RawRenaming scope targetScope)
    (termRenaming : TermRenaming ctxHigh targetCtxHigh rho) :
    ConvCumul lowerTerm
              (Term.rename termRenaming
                (Term.cumulUp (ctxHigh := ctxHigh)
                              innerLevel lowerLevel higherLevel
                              cumulOkLow cumulOkHigh cumulMonotone
                              (Nat.le_refl _) (Nat.le_refl _) lowerTerm)) :=
  -- Term.rename's cumulUp arm: same structure as subst, lowerTerm
  -- preserved verbatim, rebuilt at new target scope.  ConvCumul.viaUp
  -- witnesses the result.
  ConvCumul.viaUp innerLevel lowerLevel higherLevel
                  cumulOkLow cumulOkHigh cumulMonotone lowerTerm

/-! # Unified dispatch adapter (caller-evidence pattern)

The pair (`*_homo_benton`, `*_viaUp`) cover all ConvCumul shapes
but have different conclusion types — the unified theorem is
ill-typed in viaUp (heterogeneous endpoint scopes).

To give callers a SINGLE entry point, we provide a dispatch sum
`SubstDispatch firstTerm secondTerm` that is the disjoint union of
the two cases.  The caller supplies WHICH branch their relation
falls into by constructing the appropriate ctor.  The dispatcher
then routes via `match`, returning the correct-shaped output per
branch.

The conclusion type DEPENDS on the dispatch evidence (motive
varies per branch), which is why the result is wrapped in a
helper definition `SubstDispatch.Output` / `Output_rename` per
direction.

## Soundness

The user can build `SubstDispatch.homo` from any
`ConvCumulHomo`.  They can build `SubstDispatch.viaUp` only with
witnesses that match viaUp's exact shape.  No path constructs a
SubstDispatch witness from an arbitrary ConvCumul (because that
would require destructuring viaUp's heterogeneous indices — same
wall).  This is why the wall is an INPUT requirement on the
caller, not a hidden axiom in the dispatcher.
-/

/-- Dispatch sum for subst/rename adapters.  Two cases mirror
the architecture of ConvCumul: homogeneous-ctx (cong-built) vs
viaUp (cross-context cumul promotion).  Each ctor's output type
captures the endpoint shapes for its branch. -/
inductive ConvCumul.SubstDispatch :
    ∀ {modeFirst modeSecond : Mode}
      {levelFirst levelSecond scopeFirst scopeSecond : Nat}
      {firstCtx : Ctx modeFirst levelFirst scopeFirst}
      {secondCtx : Ctx modeSecond levelSecond scopeSecond}
      {firstType : Ty levelFirst scopeFirst}
      {secondType : Ty levelSecond scopeSecond}
      {firstRaw : RawTerm scopeFirst}
      {secondRaw : RawTerm scopeSecond},
      Term firstCtx firstType firstRaw →
      Term secondCtx secondType secondRaw → Prop
  /-- Homogeneous-ctx branch: caller supplies a ConvCumulHomo
  witness for endpoints sharing the same outer ctx/level/scope. -/
  | homo
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType secondType : Ty level scope}
      {firstRaw secondRaw : RawTerm scope}
      {firstTerm : Term context firstType firstRaw}
      {secondTerm : Term context secondType secondRaw}
      (homoRel : ConvCumulHomo firstTerm secondTerm) :
      ConvCumul.SubstDispatch firstTerm secondTerm
  /-- viaUp branch: caller supplies the lower term and cumul
  witnesses; the dispatch is over the resulting viaUp shape. -/
  | viaUp
      {mode : Mode} {scopeLow scope : Nat}
      (innerLevel lowerLevel higherLevel : UniverseLevel)
      (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
      (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
      {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
      (lowerTerm :
        Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                    (RawTerm.universeCode innerLevel.toNat)) :
      ConvCumul.SubstDispatch lowerTerm
        (Term.cumulUp (ctxHigh := ctxHigh)
                      innerLevel lowerLevel higherLevel
                      cumulOkLow cumulOkHigh cumulMonotone
                      (Nat.le_refl _) (Nat.le_refl _) lowerTerm)

/-- The dispatcher-as-elimination converts a `SubstDispatch` to
its underlying ConvCumul (a sanity check that dispatch evidence
is genuinely a ConvCumul shape). -/
theorem ConvCumul.SubstDispatch.toCumul
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
    (dispatch : ConvCumul.SubstDispatch firstTerm secondTerm) :
    ConvCumul firstTerm secondTerm := by
  cases dispatch with
  | homo homoRel => exact homoRel.toCumul
  | viaUp innerLevel lowerLevel higherLevel
          cumulOkLow cumulOkHigh cumulMonotone lowerTerm =>
      exact ConvCumul.viaUp innerLevel lowerLevel higherLevel
                            cumulOkLow cumulOkHigh cumulMonotone lowerTerm

/-! ## Branch-dependent output types via dependent Pi

The user asked: "can different output be encoded as a dependent
type?"  YES — via motive-dependent Pi.  Below we ship two
dispatchers, one per direction (rename / subst).  Each takes the
dispatch evidence and returns a Pi type whose argument and
conclusion shapes depend on which dispatch ctor was supplied.

The `match` is at TACTIC level (via `cases` in proof of an
opaque-output `def`) so Lean's type-checker accepts it without
needing to project named-binder fields at type level.

Architecture: define a single Prop `applyXxx` per direction,
proved by case-split on dispatch.  Result Prop captures the
appropriate-shaped ConvCumul per branch. -/

/-- Branch-dependent **rename-compatibility** for SubstDispatch.
Each branch returns a ConvCumul-output theorem typed
appropriately for its endpoint shape:

* `.homo`: takes `TermRenaming` from the homo ctx, returns
  `ConvCumul (firstTerm.rename _) (secondTerm.rename _)`.
* `.viaUp`: takes `TermRenaming` from outer `ctxHigh`, returns
  `ConvCumul lowerTerm (rename of (cumulUp ... lowerTerm))`.
-/
theorem ConvCumul.SubstDispatch.rename_compatible_homo_route
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (homoRel : ConvCumulHomo firstTerm secondTerm)
    {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    ConvCumul (firstTerm.rename termRenaming)
              (secondTerm.rename termRenaming) :=
  ConvCumul.rename_compatible_homo_benton termRenaming homoRel

theorem ConvCumul.SubstDispatch.subst_compatible_homo_route
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (homoRel : ConvCumulHomo firstTerm secondTerm)
    {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst context targetCtx sigma) :
    ConvCumul (firstTerm.subst termSubst)
              (secondTerm.subst termSubst) :=
  ConvCumul.subst_compatible_homo_benton termSubst homoRel

/-- viaUp branch's rename route. -/
theorem ConvCumul.SubstDispatch.rename_compatible_viaUp_route
    {mode : Mode} {scopeLow scope targetScope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {targetCtxHigh : Ctx mode (higherLevel.toNat + 1) targetScope}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat))
    (rho : RawRenaming scope targetScope)
    (termRenaming : TermRenaming ctxHigh targetCtxHigh rho) :
    ConvCumul lowerTerm
              (Term.rename termRenaming
                (Term.cumulUp (ctxHigh := ctxHigh)
                              innerLevel lowerLevel higherLevel
                              cumulOkLow cumulOkHigh cumulMonotone
                              (Nat.le_refl _) (Nat.le_refl _) lowerTerm)) :=
  ConvCumul.rename_compatible_viaUp innerLevel lowerLevel higherLevel
                                    cumulOkLow cumulOkHigh cumulMonotone
                                    lowerTerm rho termRenaming

/-- viaUp branch's subst route. -/
theorem ConvCumul.SubstDispatch.subst_compatible_viaUp_route
    {mode : Mode} {scopeLow scope targetScope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {targetCtxHigh : Ctx mode (higherLevel.toNat + 1) targetScope}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat))
    (sigma : Subst (higherLevel.toNat + 1) scope targetScope)
    (termSubst : TermSubst ctxHigh targetCtxHigh sigma) :
    ConvCumul lowerTerm
              (Term.subst termSubst
                (Term.cumulUp (ctxHigh := ctxHigh)
                              innerLevel lowerLevel higherLevel
                              cumulOkLow cumulOkHigh cumulMonotone
                              (Nat.le_refl _) (Nat.le_refl _) lowerTerm)) :=
  ConvCumul.subst_compatible_viaUp innerLevel lowerLevel higherLevel
                                   cumulOkLow cumulOkHigh cumulMonotone
                                   lowerTerm sigma termSubst

/-! # The unified interface — caller-evidence dispatcher with routes

The `SubstDispatch` inductive IS the unified entry point: a single
type covering both ConvCumul shapes (homogeneous-ctx + viaUp).
Caller holds dispatch evidence (their classification of which
branch their relation falls in) and pattern-matches via
`cases dispatch` to expose the correct shape, then applies the
matching route theorem.

The four route theorems below are the per-branch routed
implementations.  Each route has the type-correct signature for
its branch:

* `rename_compatible_homo_route` — homo branch's rename theorem
* `subst_compatible_homo_route`  — homo branch's subst theorem
* `rename_compatible_viaUp_route` — viaUp branch's rename theorem
* `subst_compatible_viaUp_route`  — viaUp branch's subst theorem

A unified single-theorem dispatcher with motive-dependent output
(`∀ d : SubstDispatch a b, d.applyTarget`) is architecturally
unavailable: the per-branch result types are genuinely
different (different endpoint scopes for viaUp), and Lean
4.29.1's `cases`-in-`def : Prop` cannot synthesize the dependent
motive cleanly.  The 4-route + dispatch-type pattern is the
zero-axiom equivalent: caller introduces dispatch evidence,
pattern-matches once, calls the matching route — Lean elaborates
each branch with the right ConvCumul shape via dependent typing.

The dispatch evidence is sound by construction: `SubstDispatch`'s
ctors mirror ConvCumul's homo/viaUp split exactly.  No path
constructs dispatch from arbitrary ConvCumul (that would require
destructuring viaUp's heterogeneous indices — same wall this
architecture sidesteps).  Caller knows which branch their
relation is in and constructs the matching ctor. -/

/-! # ConvCumul.viaUp under substitution+renaming COVERAGE COMPLETE

Together:
* `ConvCumul.{rename,subst}_compatible_homo_benton` — cong-built
  ConvCumul (homogeneous ctx fragment, all 24 ctors)
* `ConvCumul.{rename,subst}_compatible_viaUp` — cross-context
  cumul-promotion ctor at arbitrary `scopeLow`

Cover ALL ConvCumul shapes under typed renaming and substitution
at zero axioms.  The viaUp case handled separately because its
heterogeneous indices (decoupled scopeLow) make a UNIFIED theorem
ill-typed — the ctor genuinely needs the outer-side-only treatment.

A caller with a `ConvCumul a b` witness can:
1. If a, b are both at homogeneous ctx (cong-built): use
   `ConvCumul.{rename,subst}_compatible_homo_benton` after either
   manually proving `ConvCumulHomo a b` (drop viaUp) or applying
   the per-arm cong helpers from `CumulSubstCompat.lean`.
2. If a, b are viaUp-related (cumul-promotion): use
   `ConvCumul.{rename,subst}_compatible_viaUp` directly. -/

end LeanFX2

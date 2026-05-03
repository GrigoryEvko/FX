import LeanFX2.Reduction.Cumul

/-! # Reduction/ConvCumulHomo — homogeneous-context-only ConvCumul

Sister inductive to `ConvCumul` (in `Reduction/Cumul.lean`) that
EXCLUDES the `viaUp` constructor.  All remaining ctors are
HOMOGENEOUS in outer context (same `mode` / `level` / `scope` /
`ctx` on both endpoints).  Inner ctors may still be heterogeneous
in TYPE / RAW / sub-term structure (the cong rules permit this),
but never in outer-ctx parameters.

## Why this exists

The `viaUp` ctor in `ConvCumul` cross-promotes between contexts
at different levels (`ctxLow` at `lowerLevel + 1` vs `ctxHigh` at
`higherLevel + 1`).  Lean 4.29.1's dep-pattern matcher cannot
unify viaUp's heterogeneous indices when the outer relation is
constrained to homogeneous context, leading to a propositional
`lowerLevel.toNat = higherLevel.toNat` equation Lean cannot
discharge automatically.  This blocks `induction cumulRel` and
`cases cumulRel` for ConvCumul's recursive headline theorems
(Pattern 2 Benton single-rename, Pattern 3 Allais paired-env
subst — both verified empirically).

`ConvCumulHomo` sidesteps this wall by construction: drop viaUp
from the inductive.  The recursive headlines `rename_compatible`
and `subst_compatible` become trivially provable via `induction`.

The cross-context cumul-promotion case is recovered by the
existing `Conv.cumul_subst_outer` / `subst_compatible_outer`
helpers in `Reduction/Cumul.lean` (these handle the viaUp case
directly, NOT via induction).

## Bridge

`ConvCumulHomo.toCumul : ConvCumulHomo a b → ConvCumul a b` lifts
the restricted relation back to the full ConvCumul — ctor-by-ctor
trivial.

## Architecture commitment

The Pattern 2 + Pattern 3 recursive headlines defined HERE are
genuine zero-axiom theorems for the homogeneous-context fragment.
The cross-context viaUp fragment is the SEPARATE concern handled
by the per-arm helpers in `CumulSubstCompat.lean`.

The two together cover all ConvCumul shapes at zero axioms:
* Homogeneous-ctx: `ConvCumulHomo.{rename,subst}_compatible` (this file)
* Cross-ctx viaUp: `ConvCumul.subst_compatible_outer` (Cumul.lean)

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

end LeanFX2

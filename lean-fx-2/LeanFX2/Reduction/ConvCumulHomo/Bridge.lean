import LeanFX2.Reduction.ConvCumulHomo.Relation

/-! # LeanFX2.Reduction.ConvCumulHomo.Bridge

Bridge `ConvCumulHomo → ConvCumul` (ctor-by-ctor structural recursion)
plus BHKM cast-elimination primitives used by the binder/cast cases
of the Pattern 2 Benton recursive headlines.

`ConvCumul → ConvCumulHomo` is NOT generally derivable: viaUp
witnesses cannot be re-expressed as ConvCumulHomo because viaUp's
heterogeneous indices have no ConvCumulHomo analog.

## Root status

Layer 3 conv-cumul homogeneous helper. -/

namespace LeanFX2

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
  | cumulUpCong lowerLevel higherLevel cumulMonotone
                levelLeLow levelLeHigh _ ih =>
      -- ih : ConvCumul typeCodeFirst typeCodeSecond (recursed)
      exact ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
                                  levelLeLow levelLeHigh ih

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

end LeanFX2

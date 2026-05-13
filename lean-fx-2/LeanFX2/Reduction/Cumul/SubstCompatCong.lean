import LeanFX2.Reduction.Cumul.Relation

/-! # LeanFX2.Reduction.Cumul.SubstCompatCong

Per-shape subst-compatibility theorems for the structural-cong
constructors of `ConvCumul`: `appCong`, `pairCong`, `fstCong`,
`sndCong`, and `cumulUpCong`.  Each takes the ALREADY-SUBSTITUTED
inner ConvCumul relations and produces the substituted outer
ConvCumul, providing the compositional building blocks consumed by
the unified subst-compat theorem.

## Root status

Layer 3 cumulativity helper.  Consumed by `Reduction.Cumul` shim. -/

namespace LeanFX2

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

end LeanFX2

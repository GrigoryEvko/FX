import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.Normalize
import FX1Poly.Core.StronglyNormalizingConvDecision

/-! # FX1Poly/Typed/HasTypeDescPiConditionalConfluence
    — the typed Newman bridge + general typed decidable Conv, CONDITIONAL on one explicit SN hypothesis (SN-046)

The raw reduction is NOT globally strongly normalizing (`gen_natRec` / `gen_fixedPoint` are partial), so global
confluence and a general decidable Conv are NOT raw-layer theorems.  But the WELL-TYPED fragment IS strongly
normalizing — that is exactly SN-for-well-typed (SN-043), whose sole remaining gate is the universe-domain-Π
member extension (#672).  This file ships everything that strong normalization BUYS for the typed fragment, as
theorems CONDITIONAL on a single explicit hypothesis `HasTypeDescPiStronglyNormalizes` (the typed-SN interface =
#672 / SN-043).  Once #672 lands, every theorem here becomes unconditional in one step — and nothing here is
gated on #672 itself, so the bridge is shippable now without cheating.

The two consequences are pure WIRINGS of already-shipped machinery — the hard content (per-term confluence from
accessibility, the SN-fragment normal-form decider) is done; assembling it under the typed-SN interface is the
remaining structural step:

* `HasTypeDescPi.subjectConfluenceOfStronglyNormalizes` — **the typed Newman bridge (SN-046).**  Given the
  typed-SN hypothesis, any two reducts of a well-typed subject join.  `StepStar.confluence_of_localJoin_and_-
  accessible` (raw local confluence + accessibility ⟹ per-term global confluence, zero-axiom `Acc`-recursion)
  needs only the subject's SN witness, supplied here from the typed-SN hypothesis.  Newman's lemma confined to
  the SN fragment: raw global confluence (false by Ω) is never invoked.
* `Conv.decidableOfHasTypeDescPiStronglyNormalizes` — **general typed Conv is decidable** given typed-SN.  Two
  well-typed subjects are convertible-decidable via `Conv.decidableOfStronglyNormalizing` (the parameter-free
  SN-fragment decider: normalize both via `RawTerm.normalize`, compare normal forms with the propext-free
  `instDecidableEqRawTerm`).  This SUBSUMES `Conv.decidableOfIsType` (which decides only the already-normal
  TYPE classifiers of the current fragment) to ARBITRARY well-typed terms — the genuine general typed Conv,
  modulo the one SN hypothesis.

`HasTypeDescPiStronglyNormalizes` is the named typed-SN interface — the single explicit hypothesis the whole
conditional Milestone-A decidability spine rests on (the UB-SD conditional-package discipline: bundle every
typed-SN-gated result on ONE hypothesis, so #672's eventual discharge unconditionalizes all of them at once).

## Zero-axiom verification

`HasTypeDescPi.subjectConfluenceOfStronglyNormalizes` = `StepStar.confluence_of_localJoin_and_accessible` on the
hypothesis-supplied SN witness; `Conv.decidableOfHasTypeDescPiStronglyNormalizes` =
`Conv.decidableOfStronglyNormalizing` on the two hypothesis-supplied SN witnesses.  Both shipped lemmas are
zero-axiom (`Acc`-recursion, `instDecidableEqRawTerm`, no global-confluence assumption).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The typed strong-normalization interface** (= SN-043, whose gate is #672): every well-typed-Π subject is
strongly normalizing.  Stated as a named hypothesis so the conditional confluence / decidability results below
rest on ONE explicit assumption — discharged in one step once #672 (`HasPositiveMemberExtensionForStrongly-
NormalizingAllLevelTypes`) lands and feeds the shipped `HasTypeDescPi.subjectStronglyNormalizingFromFormation`
chain. -/
def HasTypeDescPiStronglyNormalizes (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeDescPi profile context subject classifier →
      StepStar.IsStronglyNormalizing subject

/-- **The typed Newman bridge (SN-046), conditional on typed-SN.**  Given the typed-SN interface, any two
reducts of a well-typed subject join: `StepStar.confluence_of_localJoin_and_accessible` turns the subject's SN
witness (raw local confluence is baked in) into per-term global confluence.  Newman's lemma confined to the
strongly-normalizing typed fragment — raw global confluence (false by Ω) is never used. -/
theorem HasTypeDescPi.subjectConfluenceOfStronglyNormalizes {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typedStronglyNormalizes : HasTypeDescPiStronglyNormalizes profile)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : StepStar subject leftReduct)
    (subjectToRight : StepStar subject rightReduct) :
    StepStar.Join leftReduct rightReduct :=
  StepStar.confluence_of_localJoin_and_accessible (typedStronglyNormalizes typed)
    subjectToLeft subjectToRight

/-- **General typed Conv is decidable, conditional on typed-SN.**  Two well-typed subjects' convertibility is
decided by the parameter-free SN-fragment decider `Conv.decidableOfStronglyNormalizing` (normalize both, compare
normal forms with the propext-free `instDecidableEqRawTerm`), fed the two SN witnesses from the typed-SN
interface.  Subsumes `Conv.decidableOfIsType` (which decides only already-normal TYPE classifiers) to ARBITRARY
well-typed terms — general typed Conv modulo the one SN hypothesis. -/
def Conv.decidableOfHasTypeDescPiStronglyNormalizes {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope}
    (typedStronglyNormalizes : HasTypeDescPiStronglyNormalizes profile)
    (leftTyped : HasTypeDescPi profile context leftSubject leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightSubject rightClassifier) :
    Decidable (Conv leftSubject rightSubject) :=
  Conv.decidableOfStronglyNormalizing
    (typedStronglyNormalizes leftTyped) (typedStronglyNormalizes rightTyped)

/-- **NbE soundness + completeness for the typed fragment, conditional on typed-SN.**  Given the typed-SN
interface, two well-typed subjects are convertible IFF `RawTerm.normalize` maps them to the SAME term.  This is
the SEMANTIC characterization underlying `Conv.decidableOfHasTypeDescPiStronglyNormalizes` (the decision is
`decidable_of_iff` over this equality): conversion on the typed fragment is EXACTLY normal-form equality — the
Path-A NbE headline (Conv ↔ quote∘eval equality), here as the raw `normalize`-equality, modulo the one SN
hypothesis.  Confluence is discharged per-term by the two SN witnesses; no global confluence is assumed. -/
theorem Conv.iff_normalize_eq_of_hasTypeDescPiStronglyNormalizes {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope}
    (typedStronglyNormalizes : HasTypeDescPiStronglyNormalizes profile)
    (leftTyped : HasTypeDescPi profile context leftSubject leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightSubject rightClassifier) :
    Conv leftSubject rightSubject ↔
      RawTerm.normalize leftSubject (typedStronglyNormalizes leftTyped)
        = RawTerm.normalize rightSubject (typedStronglyNormalizes rightTyped) :=
  Conv.iff_normalize_eq_of_isStronglyNormalizing
    (typedStronglyNormalizes leftTyped) (typedStronglyNormalizes rightTyped)

end FX1Poly.Typed

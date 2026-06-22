import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CarrierAwareFlatFormationRows
import FX1Poly.Typed.Metatheory.Canonicity.Forms.FlatCodeCanonicalForms
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors

/-! # FX1Poly/Typed/ContentFreeFlatFormationRows
    — the arrow / sum content-free flat formation FT rows over the native obligation list + FREE levels (TYTAB-4
      step 4)

The carrier-aware flat formers (product / either / equiv) are discharged in `CarrierAwareFlatFormationRows.lean`.
This file discharges the CONTENT-FREE flat formers — arrow and sum (`Generator.carrierCombinator? = none`,
`isFlatDataCode = true`).  Their reducibility-as-type is content-free: `flatCode_isReducibleTypeAtBounded`
(`FlatCodeCanonicalForms`) produces the `dataTaitCandidate` reducibility from the flat-pin alone, IGNORING the
component carriers — so there is no component-to-join cumulativity lift; only the cell's SN (from the two
components' SN) feeds the universe-membership intro.

## Per-former members (subst rides defeq on a concrete generator head)

`fundamentalArrowFlatMemberAtBoundedSucc` / `fundamentalSumFlatMemberAtBoundedSucc` are PER-FORMER (concrete
`gen_arrowCode` / `gen_sumCode`), not generic over an abstract generator: `RawTerm.subst` on a concrete `mkGen`
head reduces by DEFINITIONAL reduction (the same reason the denote-layer `arrowCodeFundamentalFromCarriers` rides
defeq), so the substituted cell's SN matches `arrowCode_isStronglyNormalizing_of_domain_codomain` /
`sumCode_isStronglyNormalizing_of_left_right` (StrongNormalizationConstructors) and its content-free reducibility
matches `flatCode_isReducibleTypeAtBounded env _ rfl rfl` (the `rfl`s discharge
`(subst σ cell).rootGenerator.isFlatDataCode = true` / `… .carrierCombinator? = none`, since the substituted cell's
root generator is the concrete one by defeq).  An abstract generator would not reduce `subst` by defeq.

## The generic two-child dispatch row + wrappers

`fundamentalTwoChildFlatRowAtBoundedSucc` factors the FREE-`levels` three-way dispatch ONCE over an opaque
`subject` + `memberBuilder` (so it serves any two-child flat former — the content-free arrow/sum here, and it
SUBSUMES the carrier-aware spine row's role).  The positional single-level case forces only the SECOND child to
`lzero` (`levelMax_zero_right`), exactly as in the carrier-aware rows.  The two wrappers
`fundamental{Arrow,Sum}FormationRowAtBoundedSucc` match the two-child spine and feed the per-former member as the
builder; the subject collapses definitionally to the concrete cell.

## Zero-axiom verification

The members are `universeMembershipIntroAtBounded` fed the per-former congruence-SN + content-free
`flatCode_isReducibleTypeAtBounded`; the dispatch row reuses `fundamentalConclusion_universeCumulative` /
`denote_le_lmaxFold` / `denote_lmaxFold_lt` / `levelMax_zero_right`.  No induction (it lives in the support layer),
no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The arrow content-free flat formation FT member (TYTAB-4 step 4).**  From the domain/codomain obligation IHs,
`arrowCode domainCode codomainCode` is a bound-reducible member of `Type@(lmaxAll [domainLevel, codomainLevel])`.
Content-free: reducibility-as-type via `flatCode_isReducibleTypeAtBounded` (ignores carriers), SN via
`arrowCode_isStronglyNormalizing_of_domain_codomain`, both riding `subst`-defeq on the concrete `gen_arrowCode`. -/
theorem fundamentalArrowFlatMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    {domainCode codomainCode : RawTerm scope}
    (domainFundamental :
      FundamentalConclusionAtBoundedSucc env bound context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtBoundedSucc env bound context codomainCode (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_arrowCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  intro _targetScope substitution envReducible
  have domainMember := domainFundamental substitution envReducible
  rw [subst_universeCodeCell] at domainMember
  have codomainMember := codomainFundamental substitution envReducible
  rw [subst_universeCodeCell] at codomainMember
  have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := domainMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := codomainMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have domainSN : IsStronglyNormalizing (RawTerm.subst substitution domainCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound domainLevel flag _ domainBelowBound domainMember
  have codomainSN : IsStronglyNormalizing (RawTerm.subst substitution codomainCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound codomainLevel flag _ codomainBelowBound codomainMember
  have outputBelowBound : LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound := by
    rw [lmaxAll_pair, LevelExpr.denote_lmax]
    exact levelMax_lt domainBelowBound codomainBelowBound
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [domainLevel, codomainLevel]) flag bound
    (.mkGen .gen_arrowCode () (.childCons (RawTerm.subst substitution domainCode)
      (.childCons (RawTerm.subst substitution codomainCode) .childNil)))
    outputBelowBound
    (arrowCode_isStronglyNormalizing_of_domain_codomain domainSN codomainSN)
    (flatCode_isReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) rfl rfl)

/-- **The sum content-free flat formation FT member (TYTAB-4 step 4).**  The sum twin of
`fundamentalArrowFlatMemberAtBoundedSucc`: `sumCode leftType rightType` is a bound-reducible member of
`Type@(lmaxAll [leftLevel, rightLevel])`, SN via `sumCode_isStronglyNormalizing_of_left_right`. -/
theorem fundamentalSumFlatMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (leftLevel rightLevel : LevelExpr) (flag : UniverseFlag)
    {leftType rightType : RawTerm scope}
    (leftFundamental :
      FundamentalConclusionAtBoundedSucc env bound context leftType (universeCodeCell leftLevel flag))
    (rightFundamental :
      FundamentalConclusionAtBoundedSucc env bound context rightType (universeCodeCell rightLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell (lmaxAll [leftLevel, rightLevel]) flag) := by
  intro _targetScope substitution envReducible
  have leftMember := leftFundamental substitution envReducible
  rw [subst_universeCodeCell] at leftMember
  have rightMember := rightFundamental substitution envReducible
  rw [subst_universeCodeCell] at rightMember
  have leftBelowBound : LevelExpr.denote leftLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := leftMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have rightBelowBound : LevelExpr.denote rightLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := rightMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have leftSN : IsStronglyNormalizing (RawTerm.subst substitution leftType) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound leftLevel flag _ leftBelowBound leftMember
  have rightSN : IsStronglyNormalizing (RawTerm.subst substitution rightType) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound rightLevel flag _ rightBelowBound rightMember
  have outputBelowBound : LevelExpr.denote (lmaxAll [leftLevel, rightLevel]) env < bound := by
    rw [lmaxAll_pair, LevelExpr.denote_lmax]
    exact levelMax_lt leftBelowBound rightBelowBound
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [leftLevel, rightLevel]) flag bound
    (.mkGen .gen_sumCode () (.childCons (RawTerm.subst substitution leftType)
      (.childCons (RawTerm.subst substitution rightType) .childNil)))
    outputBelowBound
    (sumCode_isStronglyNormalizing_of_left_right leftSN rightSN)
    (flatCode_isReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [leftLevel, rightLevel]) env) rfl rfl)

/-- **The generic two-child flat formation FT spine row (TYTAB-4 step 4).**  Factors the FREE-`levels` three-way
positional dispatch ONCE over an opaque `subject` + `memberBuilder`: from the two obligation IHs (at the positional
levels) the row lands `memberBuilder` at `Type@(lmaxAll [firstLevel, secondLevel])` and lifts to the free output
`Type@(lmaxAll levels)`.  Serves any two-child flat former (content-free arrow/sum here; subsumes the carrier-aware
spine row's role).  The `[singleLevel]` case forces only the SECOND child to `lzero` (`levelMax_zero_right`). -/
theorem fundamentalTwoChildFlatRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (flag : UniverseFlag)
    {firstCode secondCode : RawTerm scope} (subject : RawTerm scope)
    (memberBuilder : ∀ (firstLevel secondLevel : LevelExpr),
        FundamentalConclusionAtBoundedSucc env bound context firstCode (universeCodeCell firstLevel flag) →
        FundamentalConclusionAtBoundedSucc env bound context secondCode (universeCodeCell secondLevel flag) →
        FundamentalConclusionAtBoundedSucc env bound context subject
          (universeCodeCell (lmaxAll [firstLevel, secondLevel]) flag))
    {levels : List LevelExpr}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag
          (.childCons firstCode (.childCons secondCode .childNil) : RawTermChildren [0, 0] scope) levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context subject (universeCodeCell (lmaxAll levels) flag) := by
  intro targetScope substitution envReducible
  match levels with
  | firstLevel :: secondLevel :: restLevels =>
    have firstIH : FundamentalConclusionAtBoundedSucc env bound context firstCode
        (universeCodeCell firstLevel flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := firstCode,
          classifier := universeCodeCell firstLevel flag } (List.Mem.head _)
    have secondIH : FundamentalConclusionAtBoundedSucc env bound context secondCode
        (universeCodeCell secondLevel flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := secondCode,
          classifier := universeCodeCell secondLevel flag } (List.Mem.tail _ (List.Mem.head _))
    exact fundamentalConclusion_universeCumulative env bound context
      (lmaxAll [firstLevel, secondLevel])
      (lmaxAll (firstLevel :: secondLevel :: restLevels)) flag
      (memberBuilder firstLevel secondLevel firstIH secondIH)
      (denote_le_lmaxFold env restLevels (LevelExpr.lmax firstLevel secondLevel))
      (denote_lmaxFold_lt env bound restLevels (LevelExpr.lmax firstLevel secondLevel)
        (by
          rw [LevelExpr.denote_lmax]
          exact levelMax_lt (levelsBelowBound firstLevel (List.Mem.head _))
            (levelsBelowBound secondLevel (List.Mem.tail _ (List.Mem.head _))))
        (fun levelExpr levelMem =>
          levelsBelowBound levelExpr (List.Mem.tail _ (List.Mem.tail _ levelMem))))
      substitution envReducible
  | [singleLevel] =>
    have firstIH : FundamentalConclusionAtBoundedSucc env bound context firstCode
        (universeCodeCell singleLevel flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := firstCode,
          classifier := universeCodeCell singleLevel flag } (List.Mem.head _)
    have secondIH : FundamentalConclusionAtBoundedSucc env bound context secondCode
        (universeCodeCell LevelExpr.lzero flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := secondCode,
          classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.tail _ (List.Mem.head _))
    exact fundamentalConclusion_universeCumulative env bound context
      (lmaxAll [singleLevel, LevelExpr.lzero]) (lmaxAll [singleLevel]) flag
      (memberBuilder singleLevel LevelExpr.lzero firstIH secondIH)
      (by
        rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]
        exact Nat.le_of_eq (levelMax_zero_right _))
      (levelsBelowBound singleLevel (List.Mem.head _))
      substitution envReducible
  | [] =>
    have firstIH : FundamentalConclusionAtBoundedSucc env bound context firstCode
        (universeCodeCell LevelExpr.lzero flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := firstCode,
          classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
    have secondIH : FundamentalConclusionAtBoundedSucc env bound context secondCode
        (universeCodeCell LevelExpr.lzero flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := secondCode,
          classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.tail _ (List.Mem.head _))
    exact fundamentalConclusion_universeCumulative env bound context
      (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) (lmaxAll []) flag
      (memberBuilder LevelExpr.lzero LevelExpr.lzero firstIH secondIH)
      (by rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]; exact Nat.zero_le _)
      boundPositive
      substitution envReducible

/-- **The arrow content-free flat formation FT row.**  `mkGen gen_arrowCode payload children` is a bound-reducible
member of `Type@(lmaxAll levels)`; the two-child spine collapses to the arrow cell and the generic dispatch row
closes with the arrow member as the builder. -/
theorem fundamentalArrowFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_arrowCode.payload scope}
    {children : RawTermChildren Generator.gen_arrowCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_arrowCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons first (.childCons second .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_arrowCode () (.childCons first (.childCons second .childNil)))
      (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalTwoChildFlatRowAtBoundedSucc env bound context flag
      (.mkGen .gen_arrowCode () (.childCons first (.childCons second .childNil)))
      (fun firstLevel secondLevel firstFund secondFund =>
        fundamentalArrowFlatMemberAtBoundedSucc env bound context firstLevel secondLevel flag
          firstFund secondFund)
      levelsBelowBound boundPositive obligationsFundamental

/-- **The sum content-free flat formation FT row.**  `mkGen gen_sumCode payload children` is a bound-reducible
member of `Type@(lmaxAll levels)`; collapses to the sum cell with the sum member as the builder. -/
theorem fundamentalSumFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_sumCode.payload scope}
    {children : RawTermChildren Generator.gen_sumCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_sumCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons first (.childCons second .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_sumCode () (.childCons first (.childCons second .childNil)))
      (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalTwoChildFlatRowAtBoundedSucc env bound context flag
      (.mkGen .gen_sumCode () (.childCons first (.childCons second .childNil)))
      (fun firstLevel secondLevel firstFund secondFund =>
        fundamentalSumFlatMemberAtBoundedSucc env bound context firstLevel secondLevel flag
          firstFund secondFund)
      levelsBelowBound boundPositive obligationsFundamental

end FX1Poly.Typed

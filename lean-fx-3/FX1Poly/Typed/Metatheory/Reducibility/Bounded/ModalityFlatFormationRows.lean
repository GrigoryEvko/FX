import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedFormationArityDispatch
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeElementFormationRows
import FX1Poly.Typed.Engine.Formation.FlatFormerStrongNormalization

/-! # FX1Poly/Typed/ModalityFlatFormationRows
    — the cohesion-modality (ʃ / ♭ / ♯) flat formation FT members + rows over FREE levels (TYTAB-4 step 4)

The flat formation sub-family splits by `Generator.isFlatDataCode`: the 5 DATA codes (product / sum / either /
arrow / equiv, `isFlatDataCode = true`) are discharged carrier-aware / content-free in
`CarrierAwareFlatFormationRows` / `ContentFreeFlatFormationRows`.  This file discharges the remaining 3 flat
rows — the cohesion modalities `gen_shapeModality` (ʃ), `gen_flatModality` (♭), `gen_sharpModality` (♯).  They
carry a `flatTypingRuleDescOf` row (the union's flat-family formation arm types them) but are NOT data codes
(`isFlatDataCode = false`, `carrierCombinator? = none`), so their reducibility-as-type is the `neutral` arm —
a level-preserving ONE-child type former whose only semantic content is strong normalization (the modal
introduction / elimination — the unit / counit of the adjoint string — awaits the lock-extended modal context,
the context-4 frontier; this is the FORMATION leg only).

## The neutral-arm members (subst rides defeq on a concrete generator head)

`fundamental{Shape,Flat,Sharp}ModalityMemberAtBoundedSucc` are PER-FORMER (concrete `gen_shapeModality` / …),
not generic over an abstract generator: `RawTerm.subst` on a concrete `mkGen` head reduces by DEFINITIONAL
reduction (the same reason the content-free arrow/sum members ride defeq), so the substituted cell's SN matches
`flatFormerCellStronglyNormalizingOfChildren` (the flat-table SN driver) and its reducibility-as-type is the
`neutral` arm over the four table-generic root gates (`flatFormationGenerator_noWeakHeadStep`, root not Π /
universe / empty by `decide`, `isFlatDataCode = false` by `rfl`).  The level is preserved: the one-child output
`lmaxAll [childLevel]` is `childLevel` definitionally, so the member's output bound IS the child's bound.

## The generic one-child dispatch row + wrappers

`fundamentalOneChildFlatRowAtBoundedSucc` factors the FREE-`levels` two-way positional dispatch ONCE over an
opaque `subject` + `memberBuilder` (the one-child twin of `fundamentalTwoChildFlatRowAtBoundedSucc`): from the
single obligation IH (at the positional level, or forced `lzero`) the row lands `memberBuilder` at
`Type@(lmaxAll [childLevel])` and lifts to the free output `Type@(lmaxAll levels)`.  The three wrappers
`fundamental{Shape,Flat,Sharp}ModalityFormationRowAtBoundedSucc` match the one-child spine and feed the
per-former member as the builder; the subject collapses definitionally to the concrete modality cell.

## Zero-axiom verification

The members are `universeMembershipIntroAtBounded` fed the flat-table SN driver + the `neutral`-arm
reducibility (`decide` / `rfl` gates); the dispatch row reuses `fundamentalConclusion_universeCumulative` /
`denote_le_lmaxFold` / `denote_lmaxFold_lt`.  No induction (it lives in the support layer), no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The shape-modality (ʃ) flat formation FT member (TYTAB-4 step 4).**  From the carrier obligation IH,
`shapeModality childCode` is a bound-reducible member of `Type@(lmaxAll [childLevel]) = Type@childLevel` — the
`neutral`-arm reducibility (modal type formers are NOT data codes; `isFlatDataCode = false`), SN via the
flat-table SN driver, both riding `subst`-defeq on the concrete `gen_shapeModality`. -/
theorem fundamentalShapeModalityMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {childCode : RawTerm scope} (childLevel : LevelExpr) (flag : UniverseFlag)
    (childFundamental :
      FundamentalConclusionAtBoundedSucc env bound context childCode (universeCodeCell childLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_shapeModality () (.childCons childCode .childNil))
      (universeCodeCell (lmaxAll [childLevel]) flag) := by
  intro _targetScope substitution envReducible
  have childMember := childFundamental substitution envReducible
  rw [subst_universeCodeCell] at childMember
  have childBelowBound : LevelExpr.denote childLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := childMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have childSN : IsStronglyNormalizing (RawTerm.subst substitution childCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound childLevel flag _ childBelowBound childMember
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [childLevel]) flag bound
    (.mkGen .gen_shapeModality () (.childCons (RawTerm.subst substitution childCode) .childNil))
    childBelowBound
    (flatFormerCellStronglyNormalizingOfChildren flatTypingRuleDescOf_shapeModality ⟨childSN, True.intro⟩)
    ⟨IsStronglyNormalizing, ReducibleTypeStepBounded.neutral
      (flatFormationGenerator_noWeakHeadStep flatTypingRuleDescOf_shapeModality)
      (show Generator.gen_shapeModality ≠ Generator.gen_piTyCode by decide)
      (show Generator.gen_shapeModality ≠ Generator.gen_universeCode by decide)
      (show Generator.gen_shapeModality ≠ Generator.gen_emptyCode by decide) rfl⟩

/-- **The flat-modality (♭) flat formation FT member (TYTAB-4 step 4).**  The ♭ twin of
`fundamentalShapeModalityMemberAtBoundedSucc` (concrete `gen_flatModality`). -/
theorem fundamentalFlatModalityMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {childCode : RawTerm scope} (childLevel : LevelExpr) (flag : UniverseFlag)
    (childFundamental :
      FundamentalConclusionAtBoundedSucc env bound context childCode (universeCodeCell childLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_flatModality () (.childCons childCode .childNil))
      (universeCodeCell (lmaxAll [childLevel]) flag) := by
  intro _targetScope substitution envReducible
  have childMember := childFundamental substitution envReducible
  rw [subst_universeCodeCell] at childMember
  have childBelowBound : LevelExpr.denote childLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := childMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have childSN : IsStronglyNormalizing (RawTerm.subst substitution childCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound childLevel flag _ childBelowBound childMember
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [childLevel]) flag bound
    (.mkGen .gen_flatModality () (.childCons (RawTerm.subst substitution childCode) .childNil))
    childBelowBound
    (flatFormerCellStronglyNormalizingOfChildren flatTypingRuleDescOf_flatModality ⟨childSN, True.intro⟩)
    ⟨IsStronglyNormalizing, ReducibleTypeStepBounded.neutral
      (flatFormationGenerator_noWeakHeadStep flatTypingRuleDescOf_flatModality)
      (show Generator.gen_flatModality ≠ Generator.gen_piTyCode by decide)
      (show Generator.gen_flatModality ≠ Generator.gen_universeCode by decide)
      (show Generator.gen_flatModality ≠ Generator.gen_emptyCode by decide) rfl⟩

/-- **The sharp-modality (♯, the cohesion coreflective right adjoint) flat formation FT member (TYTAB-4 step
4).**  The ♯ twin of `fundamentalShapeModalityMemberAtBoundedSucc` (concrete `gen_sharpModality`). -/
theorem fundamentalSharpModalityMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {childCode : RawTerm scope} (childLevel : LevelExpr) (flag : UniverseFlag)
    (childFundamental :
      FundamentalConclusionAtBoundedSucc env bound context childCode (universeCodeCell childLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_sharpModality () (.childCons childCode .childNil))
      (universeCodeCell (lmaxAll [childLevel]) flag) := by
  intro _targetScope substitution envReducible
  have childMember := childFundamental substitution envReducible
  rw [subst_universeCodeCell] at childMember
  have childBelowBound : LevelExpr.denote childLevel env < bound := by
    obtain ⟨_, candidateReducible, _⟩ := childMember
    exact universeCodeReducibleAtBounded_belowBound candidateReducible
  have childSN : IsStronglyNormalizing (RawTerm.subst substitution childCode) :=
    stronglyNormalizing_of_universeMemberAtBounded env bound childLevel flag _ childBelowBound childMember
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [childLevel]) flag bound
    (.mkGen .gen_sharpModality () (.childCons (RawTerm.subst substitution childCode) .childNil))
    childBelowBound
    (flatFormerCellStronglyNormalizingOfChildren flatTypingRuleDescOf_sharpModality ⟨childSN, True.intro⟩)
    ⟨IsStronglyNormalizing, ReducibleTypeStepBounded.neutral
      (flatFormationGenerator_noWeakHeadStep flatTypingRuleDescOf_sharpModality)
      (show Generator.gen_sharpModality ≠ Generator.gen_piTyCode by decide)
      (show Generator.gen_sharpModality ≠ Generator.gen_universeCode by decide)
      (show Generator.gen_sharpModality ≠ Generator.gen_emptyCode by decide) rfl⟩

/-- **The generic one-child flat formation FT spine row (TYTAB-4 step 4).**  Factors the FREE-`levels` two-way
positional dispatch ONCE over an opaque `subject` + `memberBuilder`: from the single obligation IH (at the
positional level, or forced `lzero` when `levels = []`) the row lands `memberBuilder` at
`Type@(lmaxAll [childLevel])` and lifts to the free output `Type@(lmaxAll levels)`.  Serves any one-child flat
former (the cohesion modalities here).  The one-child twin of `fundamentalTwoChildFlatRowAtBoundedSucc`. -/
theorem fundamentalOneChildFlatRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (flag : UniverseFlag)
    {childCode : RawTerm scope} (subject : RawTerm scope)
    (memberBuilder : ∀ (childLevel : LevelExpr),
        FundamentalConclusionAtBoundedSucc env bound context childCode (universeCodeCell childLevel flag) →
        FundamentalConclusionAtBoundedSucc env bound context subject
          (universeCodeCell (lmaxAll [childLevel]) flag))
    {levels : List LevelExpr}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag
          (.childCons childCode .childNil : RawTermChildren [0] scope) levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context subject (universeCodeCell (lmaxAll levels) flag) := by
  intro targetScope substitution envReducible
  match levels with
  | childLevel :: restLevels =>
    have childIH : FundamentalConclusionAtBoundedSucc env bound context childCode
        (universeCodeCell childLevel flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := childCode,
          classifier := universeCodeCell childLevel flag } (List.Mem.head _)
    exact fundamentalConclusion_universeCumulative env bound context
      (lmaxAll [childLevel]) (lmaxAll (childLevel :: restLevels)) flag
      (memberBuilder childLevel childIH)
      (denote_le_lmaxFold env restLevels childLevel)
      (denote_lmaxFold_lt env bound restLevels childLevel
        (levelsBelowBound childLevel (List.Mem.head _))
        (fun levelExpr levelMem => levelsBelowBound levelExpr (List.Mem.tail _ levelMem)))
      substitution envReducible
  | [] =>
    have childIH : FundamentalConclusionAtBoundedSucc env bound context childCode
        (universeCodeCell LevelExpr.lzero flag) :=
      obligationsFundamental
        { scope := scope, context := context, subject := childCode,
          classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
    exact fundamentalConclusion_universeCumulative env bound context
      (lmaxAll [LevelExpr.lzero]) (lmaxAll []) flag
      (memberBuilder LevelExpr.lzero childIH)
      (Nat.le_refl _)
      boundPositive
      substitution envReducible

/-- **The shape-modality (ʃ) flat formation FT row.**  `mkGen gen_shapeModality payload children` is a
bound-reducible member of `Type@(lmaxAll levels)`; the one-child spine collapses to the ʃ cell and the generic
dispatch row closes with the ʃ member as the builder. -/
theorem fundamentalShapeModalityFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_shapeModality.payload scope}
    {children : RawTermChildren Generator.gen_shapeModality.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_shapeModality payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons child .childNil =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_shapeModality () (.childCons child .childNil)) (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalOneChildFlatRowAtBoundedSucc env bound context flag
      (.mkGen .gen_shapeModality () (.childCons child .childNil))
      (fun childLevel childFund =>
        fundamentalShapeModalityMemberAtBoundedSucc env bound context childLevel flag childFund)
      levelsBelowBound boundPositive obligationsFundamental

/-- **The flat-modality (♭) flat formation FT row.**  The ♭ twin of
`fundamentalShapeModalityFormationRowAtBoundedSucc`. -/
theorem fundamentalFlatModalityFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_flatModality.payload scope}
    {children : RawTermChildren Generator.gen_flatModality.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_flatModality payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons child .childNil =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_flatModality () (.childCons child .childNil)) (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalOneChildFlatRowAtBoundedSucc env bound context flag
      (.mkGen .gen_flatModality () (.childCons child .childNil))
      (fun childLevel childFund =>
        fundamentalFlatModalityMemberAtBoundedSucc env bound context childLevel flag childFund)
      levelsBelowBound boundPositive obligationsFundamental

/-- **The sharp-modality (♯) flat formation FT row.**  The ♯ twin of
`fundamentalShapeModalityFormationRowAtBoundedSucc`. -/
theorem fundamentalSharpModalityFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_sharpModality.payload scope}
    {children : RawTermChildren Generator.gen_sharpModality.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_sharpModality payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons child .childNil =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_sharpModality () (.childCons child .childNil)) (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalOneChildFlatRowAtBoundedSucc env bound context flag
      (.mkGen .gen_sharpModality () (.childCons child .childNil))
      (fun childLevel childFund =>
        fundamentalSharpModalityMemberAtBoundedSucc env bound context childLevel flag childFund)
      levelsBelowBound boundPositive obligationsFundamental

end FX1Poly.Typed

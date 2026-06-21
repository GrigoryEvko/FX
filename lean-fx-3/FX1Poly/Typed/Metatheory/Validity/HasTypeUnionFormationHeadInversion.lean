import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiDataHeadUntyped
import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiFormerInversion

/-! # FX1Poly/Typed/Metatheory/Validity/HasTypeUnionFormationHeadInversion — UNION inversions at the
    TYPE-CODE formation heads (bridge / product / either / Π)

The `HasTypeUnionInversion` recipe inverts a union typing at a concrete head `H`.  The shipped instances
target INTRO heads (`lam` / `optionSome` / …) and ELIM heads (`fst` / `snd` / …), where the `formationRule`
arm DIES (the table can not produce an intro / elim head).  This file inverts at the TYPE-CODE formation
heads — bridge (`.termIndexed gen_bridgeCode`, carrier leg), product / either (`.flat`, both components),
and Π (`.cumulative gen_piTyCode`, codomain leg) — where the `formationRule` arm SURVIVES (the code IS a
formation row), so the surviving disjunct surfaces the row's child obligations.  These feed the union
classifier-validity elim-output discharges (`pathApp` / `fst` / `snd` / `app`) and the `bridgeFormed` data
former, ALL now unconditional after the kernel-wide free-`levels` fix.

## All type-code-head inversions are now TOTAL (the kernel-wide free-`levels` fix)

`bridgeTypeCell` (`gen_bridgeCode`) is `typingRuleDescOf … = none`, so the `ofGrown` arm is REFUTED by
`cellHasNoTypingWhenRootGenericallyExcluded`, leaving the `formationRule` arm as the SOLE survivor.  Its
TERM-INDEXED obligation list ALWAYS begins with the CARRIER obligation (read from the `level` PARAMETER, not
the `levels` LIST).

The FLAT product / either heads were once blocked by a degenerate `levels = []` escape: `flatFormationObligations`
read child obligations POSITIONALLY from the FREE `levels` list, so a `levels = []` flat typing carried NO
component obligations.  **That hole is now CLOSED kernel-wide** (`flatFormationObligations` /
`cumulativeFormationObligations` FORCE every child to be a type at `Type@0` when `levels` is exhausted, instead
of degenerating to `[]`).  So the flat (product / either) and cumulative (Π / Σ / List / Option) obligation
lists ALWAYS carry every child-at-universe obligation — for ANY `levels` — and every type-code-head inversion
(product / either / Π) is now TOTAL, exactly like the term-indexed bridge / Id heads.  This closes
`fstOutputFormed` / `sndOutputFormed` (product inversion), feeds `eitherFormed`-side reasoning (either
inversion), and the Π-codomain inversion below feeds `app` / `eitherMatch`.

## Zero-axiom

`induction` over the 5 union arms (the `HasTypeUnionInversion` recipe) + the host head refutation
(`cellHasNoTypingWhenRootGenericallyExcluded`) + the term-indexed carrier obligation read via `List.Mem.head`
+ `cases` on `List.Mem`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **★ Inversion at the bridge type-code head, carrier leg.**  A union typing of a `bridgeTypeCell carrier
left right`-headed subject surfaces the CARRIER validity: `carrier` inhabits a universe code.  No grown
disjunct (`bridgeTypeCell` is untyped in the grown engine); the surviving `formationRule` arm's term-indexed
obligation list always opens with the carrier-at-universe obligation (read from the `level` parameter, not the
`levels` list — so total, unlike the flat product / either heads).  Feeds `pathAppOutputFormed`. -/
theorem HasTypeUnion.invertAtBridgeCodeHeadCarrier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {carrierCode leftEndpoint rightEndpoint : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :
    ∃ (carrierLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeUnion profile context carrierCode (universeCodeCell carrierLevel flag) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      exact innerInversion subjectShape
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd
        (hostTyped.cellHasNoTypingWhenRootGenericallyExcluded
          (by intro contra; cases contra) (by intro contra; cases contra)
          (by intro contra; cases contra) (by intro contra; cases contra) rfl)
        (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold =>
      -- The bridge code IS a term-indexed formation row — this arm SURVIVES.  Pin the generator via the
      -- subject head, force the rule, recover the children, and read the carrier obligation (always first).
      have headEq : generator = Generator.gen_bridgeCode :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      obtain rfl : rule = FormationRule.termIndexed { outputType := termIndexedCarrierOutput } :=
        Option.some.inj isFormationRule.symm
      match children, subjectShape with
      | .childCons childCarrier (.childCons childLeft (.childCons childRight .childNil)),
        subjectShape =>
          -- `subjectShape` now forces `childCarrier = carrierCode` (+ the two endpoints); destructure it.
          rcases subjectShape with ⟨⟩
          -- The term-indexed obligation list opens with `carrierCode : universeCodeCell level flag`; read it.
          refine ⟨level, flag, ?_⟩
          exact premisesHold _ (List.Mem.head _)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-! ## ★ TYTAB-2 wave W4: the FLAT-former (product / either) head inversions — NOW TOTAL

After the kernel-wide free-`levels` fix (`flatFormationObligations` / `cumulativeFormationObligations` FORCE
every child to be a type at `Type@0` when `levels` is exhausted, instead of degenerating to `[]`), the
`.flat` formation row's obligation list ALWAYS carries BOTH child-at-universe obligations — for ANY `levels`.
So a `productTypeCell` / `eitherTypeCell` union typing's component validities are recoverable
UNCONDITIONALLY, exactly as the bridge carrier was.  These inversions close `fstOutputFormed` /
`sndOutputFormed` / `eitherFormed` / `productFormed`. -/

/-- **★ Inversion at the product type-code head.**  A union typing of a `productTypeCell firstType
secondType`-headed subject surfaces BOTH component validities: each inhabits a universe code.  No grown
disjunct (`productTypeCell` is host-untyped); the surviving `formationRule` arm's flat obligation list now
ALWAYS carries both child-at-universe obligations (the free-`levels` fix), so the inversion is TOTAL.  Feeds
`fstOutputFormed` / `sndOutputFormed`. -/
theorem HasTypeUnion.invertAtProductCodeHeadComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstType secondType : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = productTypeCell firstType secondType) :
    (∃ (firstLevel : LevelExpr) (flag : UniverseFlag),
        HasTypeUnion profile context firstType (universeCodeCell firstLevel flag)) ∧
    (∃ (secondLevel : LevelExpr) (flag : UniverseFlag),
        HasTypeUnion profile context secondType (universeCodeCell secondLevel flag)) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      exact innerInversion subjectShape
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd
        (hostTyped.cellHasNoTypingWhenRootGenericallyExcluded
          (by intro contra; cases contra) (by intro contra; cases contra)
          (by intro contra; cases contra) (by intro contra; cases contra) rfl)
        (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold =>
      have headEq : generator = Generator.gen_productCode :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      obtain rfl : rule = FormationRule.flat { outputType := universeFormerOutput } :=
        Option.some.inj isFormationRule.symm
      match children, subjectShape with
      | .childCons childFirst (.childCons childSecond .childNil), subjectShape =>
          rcases subjectShape with ⟨⟩
          -- The flat obligation list ALWAYS opens with both child-at-universe obligations (free-`levels` fix);
          -- read each off, the level being the matching `levels` entry or the forced `lzero`.
          cases levels with
          | nil =>
              exact ⟨⟨LevelExpr.lzero, flag, premisesHold _ (List.Mem.head _)⟩,
                LevelExpr.lzero, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
          | cons firstLevel restLevels =>
              cases restLevels with
              | nil =>
                  exact ⟨⟨firstLevel, flag, premisesHold _ (List.Mem.head _)⟩,
                    LevelExpr.lzero, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
              | cons secondLevel _ =>
                  exact ⟨⟨firstLevel, flag, premisesHold _ (List.Mem.head _)⟩,
                    secondLevel, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-- **★ Inversion at the either type-code head.**  The `eitherTypeCell` twin of
`invertAtProductCodeHeadComponents` — both component validities recovered (the flat obligation list is now
total).  Feeds `eitherFormed`. -/
theorem HasTypeUnion.invertAtEitherCodeHeadComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {leftType rightType : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherTypeCell leftType rightType) :
    (∃ (leftLevel : LevelExpr) (flag : UniverseFlag),
        HasTypeUnion profile context leftType (universeCodeCell leftLevel flag)) ∧
    (∃ (rightLevel : LevelExpr) (flag : UniverseFlag),
        HasTypeUnion profile context rightType (universeCodeCell rightLevel flag)) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      exact innerInversion subjectShape
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd
        (hostTyped.cellHasNoTypingWhenRootGenericallyExcluded
          (by intro contra; cases contra) (by intro contra; cases contra)
          (by intro contra; cases contra) (by intro contra; cases contra) rfl)
        (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold =>
      have headEq : generator = Generator.gen_eitherCode :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      obtain rfl : rule = FormationRule.flat { outputType := universeFormerOutput } :=
        Option.some.inj isFormationRule.symm
      match children, subjectShape with
      | .childCons childLeft (.childCons childRight .childNil), subjectShape =>
          rcases subjectShape with ⟨⟩
          cases levels with
          | nil =>
              exact ⟨⟨LevelExpr.lzero, flag, premisesHold _ (List.Mem.head _)⟩,
                LevelExpr.lzero, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
          | cons firstLevel restLevels =>
              cases restLevels with
              | nil =>
                  exact ⟨⟨firstLevel, flag, premisesHold _ (List.Mem.head _)⟩,
                    LevelExpr.lzero, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
              | cons secondLevel _ =>
                  exact ⟨⟨firstLevel, flag, premisesHold _ (List.Mem.head _)⟩,
                    secondLevel, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

/-- **★ Inversion at the Π type-code head, codomain leg.**  A union typing of a `piTyCodeCell domainCode
codomainCode`-headed subject surfaces the CODOMAIN-UNDER-BINDER validity: `codomainCode` inhabits a universe
code in the domain-extended context `context.cons domainCode`.  TWO surviving arms (`piTyCodeCell` IS
host-typeable, so `ofGrown` is NOT refuted): the `ofGrown` arm routes through the host `invertPiTyCode` (whose
codomain typing re-embeds via `ofGrown`); the `formationRule` arm reads the cumulative codomain obligation
(now FORCED for any `levels` by the free-`levels` fix).  Feeds the `app` substitution discharge and the
`eitherMatch` handler discharge. -/
theorem HasTypeUnion.invertAtPiCodeHeadCodomain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = piTyCodeCell domainCode codomainCode) :
    ∃ (codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeUnion profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      exact innerInversion subjectShape
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped, _convToCode⟩ :=
        HasTypeDescPi.invertPiTyCode hostTyped
      exact ⟨codomainLevel, flag, HasTypeUnion.ofGrown codomainTyped⟩
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold =>
      have headEq : generator = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      obtain rfl : rule = FormationRule.cumulative { outputType := universeFormerOutput } :=
        Option.some.inj isFormationRule.symm
      match children, subjectShape with
      | .childCons childDomain (.childCons childCodomain .childNil), subjectShape =>
          rcases subjectShape with ⟨⟩
          -- The cumulative Π obligation list is [domain (ambient), codomain (binder-extended)] — both FORCED
          -- for any `levels` (the free-`levels` fix).  Read the codomain obligation (index 1).
          cases levels with
          | nil =>
              exact ⟨LevelExpr.lzero, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
          | cons domainLevel restLevels =>
              cases restLevels with
              | nil =>
                  exact ⟨LevelExpr.lzero, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
              | cons codomainLevel _ =>
                  exact ⟨codomainLevel, flag, premisesHold _ (List.Mem.tail _ (List.Mem.head _))⟩
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params isElim premisesHold =>
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact absurd ((elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)

end FX1Poly.Typed

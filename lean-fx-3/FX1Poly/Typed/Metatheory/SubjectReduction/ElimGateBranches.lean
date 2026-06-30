import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateReassemble
import FX1Poly.Typed.Metatheory.Validity.IntervalNotConvRigidHeads
import FX1Poly.Typed.Metatheory.SubjectReduction.CleanElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.RecursorElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.UsabilityHoldsUnderObligationsDrift
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimGateBranches
    — SR-DSL-5: the SPINE-ALIGNED per-generator branches of the eliminator-congruence gate

`UnionElimCongruenceCloses` (HasTypeUnionCongruenceClosesGeneric.lean) dispatches on the eliminator generator.
This file ships the per-generator BRANCH lemmas: each proves the gate conclusion for ONE eliminator, given the
gate's hypotheses specialized to that rule.  The shape is uniform per row:

  1. destructure the rule's `args` / `params` (a fixed `childCons` shape from the rule's arity);
  2. reduce `memberCell scope args` to its `mkGen genX payloadX args` form and inject the gate's `memberCell =
     mkGen reformed…` equation to pin `reformedGenerator = genX`, `reformedPayload = payloadX`,
     `childrenBefore = args`;
  3. derive the per-obligation classifier-formedness witnesses the row's `*ObligationsDriftUnderArgStep` needs
     (`classifierIsType` over `WfContextUnion` for the typed obligations; `universeFormation` for the universe-code
     ones);
  4. build the obligation drift + output drift and hand them to the generic `elimGateRowReassemble`;
  5. bridge `memberCell scope childrenAfter = mkGen genX payloadX childrenAfter` (the reformed cell) by the same
     `childCons`-shape reduction.

## The cell-spine vs rule-args alignment requirement (SR-DSL-5 design constraint)

Step (5)'s bridge `rule.memberCell scope X = RawTerm.mkGen generator () X` holds DEFINITIONALLY exactly when the
row's emitted cell spine equals the rule's `args` order — i.e. `<row>Cell` lays its `childCons` spine out in the
SAME order the `memberCell` match binds them.  This holds for NINE of the eleven rows:

  * the four base rows — `fst` (`fstCell pairTerm`), `snd`, `app` (`appCell function argument`), `pathApp`; and
  * the five dependent rows whose scrutinee/witness is LAST in BOTH `args` and spine — `optionMatch`
    (`optionMatchCell motive none some scrutinee`), `eitherMatch`, `natElim` (`natElimCell motive zeroBranch
    succBranch scrutinee`), `natRec`, `idJ` (`idJCell motive baseCase witness`).

For those nine the gate's `childrenBefore` IS `args`, so the `mkGen` bridge `cases childrenAfter …; rfl` discharges
and the args-ordered `*ObligationsDriftUnderArgStep` / output-drift families apply with the gate's `childStep`
passed directly.

The TWO permuting rows — `boolElim` and `listElim` — put scrutinee at `args` position 1 but emit it LAST in the
cell spine: `boolElimCell motive scrutinee thenBranch elseBranch` emits `(motive, thenBranch, elseBranch,
scrutinee)`; `listElimCell motive scrutinee nilBranch consBranch` emits `(motive, nilBranch, consBranch,
scrutinee)`.  There the gate's `childrenBefore` is the cell SPINE, not `args`, so `memberCell scope X ≠ mkGen
generator () X`.  Those two use a spine-aligned rebuild: case the spine `StepChildren` per position, identify which
`args` position stepped (the fixed permutation `spine0↦args0`, `spine1↦args2`, `spine2↦args3`, `spine3↦args1`), feed
the args-ordered obligation / output drift at the reindexed `StepChildren`, and let `elimGateRowReassemble`'s
`memberCell scope argsAfter` conclusion unify with the goal's stepped spine by `isDefEq`.

## Zero-axiom

`HasTypeUnion.classifierIsType` + the row drift lemma + `elimGateRowReassemble` + the `mkGen` injection recipe
(`injection` / `eq_of_heq` / `subst`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## (A1-CONJUNCT-WIRE) head-stability refuters — `intervalTypeCell ≢ <former>`

Each rigid type former is head-stable to its own generator under reduction, and `intervalTypeCell` is head-stable
to `gen_intervalCode`; so global confluence (`Conv.refutedByDistinctStableHeads`) refutes any conversion between
them.  These feed the typed-at-non-interval bridge (`typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval`):
an obligation subject typed at one of these formers is fibrantly usable, because it cannot sit at a `lockCons`-0
position (whose lookup is the interval).  Local (`private`) so they do not collide with the per-congruence twins
under the audit bundle. -/

private theorem intervalNotConvProductCode {scope : Nat} (firstType secondType : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (productTypeCell firstType secondType) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_productTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvPiCode {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (piTyCodeCell domainCode codomainCode) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_piTyCodeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvBridgeCode {scope : Nat}
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_bridgeTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvNatCode {scope : Nat} :
    ¬ Conv (intervalTypeCell : RawTerm scope) natTypeCell :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_natTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvBoolCode {scope : Nat} :
    ¬ Conv (intervalTypeCell : RawTerm scope) boolTypeCell :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_boolTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvOptionCode {scope : Nat} (elementType : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (optionTypeCell elementType) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_optionTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvEitherCode {scope : Nat} (leftType rightType : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (eitherTypeCell leftType rightType) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_eitherTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvListCode {scope : Nat} (elementType : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (listTypeCell elementType) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_listTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

private theorem intervalNotConvIdCode {scope : Nat} (typeCode leftEndpoint rightEndpoint : RawTerm scope) :
    ¬ Conv (intervalTypeCell : RawTerm scope) (idTypeCell typeCode leftEndpoint rightEndpoint) :=
  fun convertibility => Conv.refutedByDistinctStableHeads convertibility
    (fun _reduct chain => headReaches_intervalTypeCell chain)
    (fun _reduct chain => headReaches_idTypeCell chain)
    (fun headsEqual => Generator.noConfusion headsEqual)

/-! ## (A1-CONJUNCT-WIRE) the per-row usability discharge helpers

Each helper proves the `elimGateRowReassemble` `usabilityAfter` obligation for ONE row at a generic `argsAfter`:
it `cases argsAfter` to expose the cell spine, peels the (now-concrete) obligation list, and for each obligation
subject proves `isSubjectUsableAtModality subject modality = true`.  RIGID-classifier obligations (the scrutinee at
its data code, the function at its Π code, the Π-typed branches, every universe-code subject) discharge through the
typed-at-non-interval bridge applied to the drifted typing `premisesAfter`.  The genuinely-HARD obligations — whose
classifier is a free `subst0 motive X` / an arbitrary carrier / the affine interval, none provably `≢` interval —
take a "typed-implies-usable" RESIDUAL hypothesis (the bridge ASSUMED for that classifier), discharged up-thread
from the original eliminator's `usabilityHolds`.  The residuals are quantified over the drifting `motiveVariant`
so they apply whether or not the motive stepped. -/

private theorem fstUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (firstType secondType : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    {argsAfter : RawTermChildren fstElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ fstElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ fstElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons pairAfter restAfter =>
    cases restAfter
    intro obligation hmem
    cases hmem with
    | head =>
        exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
          (WfContextUnion.allLocksAreInterval context wellFormed)
          (intervalNotConvProductCode firstType secondType) (premisesAfter _ (List.Mem.head _))
    | tail _ hmem => cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalTypeCell_not_conv_universeCodeCell level0 flag)
            (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
      | tail _ hmem => cases hmem

private theorem sndUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (firstType secondType : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    {argsAfter : RawTermChildren sndElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ sndElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ sndElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons pairAfter restAfter =>
    cases restAfter
    intro obligation hmem
    cases hmem with
    | head =>
        exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
          (WfContextUnion.allLocksAreInterval context wellFormed)
          (intervalNotConvProductCode firstType secondType) (premisesAfter _ (List.Mem.head _))
    | tail _ hmem => cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalTypeCell_not_conv_universeCodeCell level0 flag)
            (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
      | tail _ hmem => cases hmem

private theorem appUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (argumentReductUsable : ∀ {subject : RawTerm scope},
      HasTypeUnion profile context subject domainCode →
        context.isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren appElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ appElimRule.obligations scope context argsAfter
        (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ appElimRule.obligations scope context argsAfter
        (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons functionAfter rest1 => cases rest1 with
    | childCons argumentAfter rest2 =>
      cases rest2
      intro obligation hmem
      cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalNotConvPiCode domainCode codomainCode) (premisesAfter _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head => exact argumentReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem

private theorem pathAppUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (carrierCode leftEndpoint rightEndpoint : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (argumentReductUsable : ∀ {subject : RawTerm scope},
      HasTypeUnion profile context subject intervalTypeCell →
        context.isSubjectUsableAtModality subject .dimensional = true)
    {argsAfter : RawTermChildren pathAppElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ pathAppElimRule.obligations scope context argsAfter
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ pathAppElimRule.obligations scope context argsAfter
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons pathAfter rest1 => cases rest1 with
    | childCons argumentAfter rest2 =>
      cases rest2
      intro obligation hmem
      cases hmem with
      | head =>
          exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
            (WfContextUnion.allLocksAreInterval context wellFormed)
            (intervalNotConvBridgeCode carrierCode leftEndpoint rightEndpoint)
            (premisesAfter _ (List.Mem.head _))
      | tail _ hmem => cases hmem with
        | head => exact argumentReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
        | tail _ hmem => cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed)
                (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          | tail _ hmem => cases hmem

private theorem boolElimUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (thenReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (RawTerm.subst0 motiveVariant (RawTerm.mkGen .gen_boolTrue () .childNil)) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    (elseReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (RawTerm.subst0 motiveVariant (RawTerm.mkGen .gen_boolFalse () .childNil)) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren boolElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ boolElimRule.obligations scope context argsAfter .childNil level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ boolElimRule.obligations scope context argsAfter .childNil level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons scrutineeAfter rest2 => cases rest2 with
      | childCons thenAfter rest3 => cases rest3 with
        | childCons elseAfter rest4 =>
          cases rest4
          intro obligation hmem
          cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed) intervalNotConvBoolCode
                (premisesAfter _ (List.Mem.head _))
          | tail _ hmem => cases hmem with
            | head => exact thenReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hmem => cases hmem with
              | head =>
                  exact elseReductUsable
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem with
                | head =>
                    exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                      (TypingContext.AllLocksAreInterval.cons
                        (WfContextUnion.allLocksAreInterval context wellFormed))
                      (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                      (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                | tail _ hmem => cases hmem

private theorem optionMatchUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (typeParamA typeParamB : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (noneReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (RawTerm.subst0 motiveVariant optionNoneCell) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren optionMatchElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ optionMatchElimRule.obligations scope context argsAfter
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ optionMatchElimRule.obligations scope context argsAfter
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons noneAfter rest2 => cases rest2 with
      | childCons someAfter rest3 => cases rest3 with
        | childCons scrutineeAfter rest4 =>
          cases rest4
          intro obligation hmem
          cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed)
                (intervalNotConvOptionCode typeParamA) (premisesAfter _ (List.Mem.head _))
          | tail _ hmem => cases hmem with
            | head => exact noneReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hmem => cases hmem with
              | head =>
                  exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                    (WfContextUnion.allLocksAreInterval context wellFormed)
                    (intervalNotConvPiCode typeParamA _)
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem with
                | head =>
                    exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                      (TypingContext.AllLocksAreInterval.cons
                        (WfContextUnion.allLocksAreInterval context wellFormed))
                      (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                      (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                | tail _ hmem => cases hmem

private theorem eitherMatchUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (typeParamA typeParamB : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    {argsAfter : RawTermChildren eitherMatchElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ eitherMatchElimRule.obligations scope context argsAfter
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ eitherMatchElimRule.obligations scope context argsAfter
        (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons leftAfter rest2 => cases rest2 with
      | childCons rightAfter rest3 => cases rest3 with
        | childCons scrutineeAfter rest4 =>
          cases rest4
          intro obligation hmem
          cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed)
                (intervalNotConvEitherCode typeParamA typeParamB) (premisesAfter _ (List.Mem.head _))
          | tail _ hmem => cases hmem with
            | head =>
                exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                  (WfContextUnion.allLocksAreInterval context wellFormed)
                  (intervalNotConvPiCode typeParamA _)
                  (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hmem => cases hmem with
              | head =>
                  exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                    (WfContextUnion.allLocksAreInterval context wellFormed)
                    (intervalNotConvPiCode typeParamB _)
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem with
                | head =>
                    exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                      (TypingContext.AllLocksAreInterval.cons
                        (WfContextUnion.allLocksAreInterval context wellFormed))
                      (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                      (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                | tail _ hmem => cases hmem

private theorem natElimUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (baseReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (RawTerm.subst0 motiveVariant natZeroCell) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    (stepReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm (scope + 2)},
      HasTypeUnion profile ((context.cons natTypeCell).cons motiveVariant) subject
          (natElimDependentSuccBranchType motiveVariant) →
        ((context.cons natTypeCell).cons motiveVariant).isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren natElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ natElimRule.obligations scope context argsAfter .childNil level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ natElimRule.obligations scope context argsAfter .childNil level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons baseAfter rest2 => cases rest2 with
      | childCons stepAfter rest3 => cases rest3 with
        | childCons scrutineeAfter rest4 =>
          cases rest4
          intro obligation hmem
          cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed) intervalNotConvNatCode
                (premisesAfter _ (List.Mem.head _))
          | tail _ hmem => cases hmem with
            | head => exact baseReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hmem => cases hmem with
              | head =>
                  exact stepReductUsable
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem with
                | head =>
                    exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                      (TypingContext.AllLocksAreInterval.cons
                        (WfContextUnion.allLocksAreInterval context wellFormed))
                      (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                      (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                | tail _ hmem => cases hmem

private theorem natRecUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (baseReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (RawTerm.subst0 motiveVariant natZeroCell) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    (stepReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm (scope + 2)},
      HasTypeUnion profile ((context.cons natTypeCell).cons motiveVariant) subject
          (natElimDependentSuccBranchType motiveVariant) →
        ((context.cons natTypeCell).cons motiveVariant).isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren natRecElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ natRecElimRule.obligations scope context argsAfter .childNil level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ natRecElimRule.obligations scope context argsAfter .childNil level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons baseAfter rest2 => cases rest2 with
      | childCons stepAfter rest3 => cases rest3 with
        | childCons scrutineeAfter rest4 =>
          cases rest4
          intro obligation hmem
          cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed) intervalNotConvNatCode
                (premisesAfter _ (List.Mem.head _))
          | tail _ hmem => cases hmem with
            | head => exact baseReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hmem => cases hmem with
              | head =>
                  exact stepReductUsable
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem with
                | head =>
                    exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                      (TypingContext.AllLocksAreInterval.cons
                        (WfContextUnion.allLocksAreInterval context wellFormed))
                      (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                      (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                | tail _ hmem => cases hmem

private theorem idJUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (typeCode leftEndpoint rightEndpoint : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (rightEndpointReductUsable : ∀ {subject : RawTerm scope},
      HasTypeUnion profile context subject typeCode →
        context.isSubjectUsableAtModality subject .fibrant = true)
    (baseCaseReductUsable : ∀ {motiveVariant : RawTerm (scope + 2)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (idJMotiveAt motiveVariant leftEndpoint (reflCell leftEndpoint)) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren idJElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ idJElimRule.obligations scope context argsAfter
        (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil))) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ idJElimRule.obligations scope context argsAfter
        (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil))) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons baseCaseAfter rest2 => cases rest2 with
      | childCons witnessAfter rest3 =>
        cases rest3
        intro obligation hmem
        cases hmem with
        | head =>
            exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
              (WfContextUnion.allLocksAreInterval context wellFormed)
              (intervalNotConvIdCode typeCode leftEndpoint rightEndpoint) (premisesAfter _ (List.Mem.head _))
        | tail _ hmem => cases hmem with
          | head => exact rightEndpointReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ hmem => cases hmem with
            | head =>
                exact baseCaseReductUsable
                  (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            | tail _ hmem => cases hmem with
              | head =>
                  exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                    (TypingContext.AllLocksAreInterval.cons (TypingContext.AllLocksAreInterval.cons
                      (WfContextUnion.allLocksAreInterval context wellFormed)))
                    (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
              | tail _ hmem => cases hmem

private theorem listElimUsabilityDischarge {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (elementType resultType : RawTerm scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag) (wellFormed : WfContextUnion context)
    (nilReductUsable : ∀ {motiveVariant : RawTerm (scope + 1)} {subject : RawTerm scope},
      HasTypeUnion profile context subject (RawTerm.subst0 motiveVariant listNilCell) →
        context.isSubjectUsableAtModality subject .fibrant = true)
    {argsAfter : RawTermChildren listElimRule.argShifts scope}
    (premisesAfter : ∀ obligation ∈ listElimRule.obligations scope context argsAfter
        (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ listElimRule.obligations scope context argsAfter
        (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  cases argsAfter with
  | childCons motiveAfter rest1 => cases rest1 with
    | childCons scrutineeAfter rest2 => cases rest2 with
      | childCons nilAfter rest3 => cases rest3 with
        | childCons consAfter rest4 =>
          cases rest4
          intro obligation hmem
          cases hmem with
          | head =>
              exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                (WfContextUnion.allLocksAreInterval context wellFormed)
                (intervalNotConvListCode elementType) (premisesAfter _ (List.Mem.head _))
          | tail _ hmem => cases hmem with
            | head => exact nilReductUsable (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
            | tail _ hmem => cases hmem with
              | head =>
                  exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                    (WfContextUnion.allLocksAreInterval context wellFormed)
                    (intervalNotConvPiCode elementType _)
                    (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              | tail _ hmem => cases hmem with
                | head =>
                    exact typedAtNonIntervalImpliesFibrantlyUsable_ofLocksInterval
                      (TypingContext.AllLocksAreInterval.cons
                        (WfContextUnion.allLocksAreInterval context wellFormed))
                      (intervalTypeCell_not_conv_universeCodeCell level0 flag)
                      (premisesAfter _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
                | tail _ hmem => cases hmem

/-- **The `fst` branch of the eliminator-congruence gate.**  A stepped `fst` cell re-types at its (param) output
type, `Conv`-equal to the original.  The pair obligation's classifier (`productTypeCell firstType secondType`) is
formed via `classifierIsType` over `WfContextUnion`; the self-certifying `firstType : universeCode` obligation gives
the second formedness directly via `universeFormation`; the output `firstType` is a param, so the output drift is
`Conv.refl`. -/
theorem fstElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren fstElimRule.argShifts scope) (params : RawTermChildren fstElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ fstElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : fstElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (fstElimRule.outputType scope args params) := by
  match args, params with
  | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType) :=
      premisesHold _ (List.Mem.head _)
    have pairClassifierFormed : UnionClassifierIsType profile context
        (productTypeCell firstType secondType) :=
      (HasTypeUnion.classifierIsPretype pairTyped wellFormed).resolveType
        (productTypeCell_not_conv_intervalTypeCell firstType secondType)
    have firstTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : fstElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_fst () childrenAfter := by
      cases childrenAfter with
      | childCons headAfter restAfter => cases restAfter; rfl
    have drift := fstObligationsDriftUnderArgStep level0 level1 flag pairClassifierFormed
      firstTypeClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_fst fstElimRule
      (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction drift (Conv.refl _)
      (fstUsabilityDischarge firstType secondType level0 level1 flag wellFormed
        (premisesHoldUnderObligationsDrift drift childSubjectReduction premisesHold))

/-- **The `snd` branch** — the `fst` twin at the second projection (output `secondType`, a param). -/
theorem sndElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren sndElimRule.argShifts scope) (params : RawTermChildren sndElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ sndElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : sndElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (sndElimRule.outputType scope args params) := by
  match args, params with
  | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType) :=
      premisesHold _ (List.Mem.head _)
    have pairClassifierFormed : UnionClassifierIsType profile context
        (productTypeCell firstType secondType) :=
      (HasTypeUnion.classifierIsPretype pairTyped wellFormed).resolveType
        (productTypeCell_not_conv_intervalTypeCell firstType secondType)
    have secondTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : sndElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_snd () childrenAfter := by
      cases childrenAfter with
      | childCons headAfter restAfter => cases restAfter; rfl
    have drift := sndObligationsDriftUnderArgStep level0 level1 flag pairClassifierFormed
      secondTypeClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_snd sndElimRule
      (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction drift (Conv.refl _)
      (sndUsabilityDischarge firstType secondType level0 level1 flag wellFormed
        (premisesHoldUnderObligationsDrift drift childSubjectReduction premisesHold))

/-- **The `app` branch** — the mixed-output row: output `subst0 codomainCode argument` drifts when the `argument`
child steps (`appOutputTypeDriftUnderArgStep`); a function step leaves it fixed.  Both obligation classifiers
(`piTyCode` / `domainCode`) are formed via `classifierIsType` over the well-formed context. -/
theorem appElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren appElimRule.argShifts scope) (params : RawTermChildren appElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ appElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: the before-args obligation subjects are fibrantly usable (the native `elim` arm's
    -- `usabilityHolds`, threaded from the gate).  The drifted after-args subjects stay usable by the unconditional
    -- step-preservation driver `usabilityHoldsUnderObligationsDrift` — no oracle, no interval refuter needed.
    (usabilityHolds : ∀ obligation ∈ appElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : appElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (appElimRule.outputType scope args params) := by
  match args, params with
  | .childCons function (.childCons argument .childNil), .childCons domainCode (.childCons codomainCode .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have functionTyped : HasTypeUnion profile context function (piTyCodeCell domainCode codomainCode) :=
      premisesHold _ (List.Mem.head _)
    have argumentTyped : HasTypeUnion profile context argument domainCode :=
      premisesHold _ (List.Mem.tail _ (List.Mem.head _))
    have functionClassifierFormed : UnionClassifierIsType profile context
        (piTyCodeCell domainCode codomainCode) :=
      (HasTypeUnion.classifierIsPretype functionTyped wellFormed).resolveType
        (piTyCodeCell_not_conv_intervalTypeCell domainCode codomainCode)
    have argumentClassifierFormed : UnionClassifierIsType profile context domainCode :=
      HasTypeUnion.classifierIsType argumentTyped wellFormed
    have memberAfterEq : appElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_app () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    have drift := appObligationsDriftUnderArgStep level0 level1 flag functionClassifierFormed
      argumentClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_app appElimRule
      (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction drift
      (appOutputTypeDriftUnderArgStep function domainCode codomainCode childStep)
      (usabilityHoldsUnderObligationsDrift drift childSubjectReduction
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-- **The `pathApp` branch** — output `carrierCode`, a param (`Conv.refl`).  Path / interval-argument obligations
formed via `classifierIsType`; the self-certifying carrier obligation via `universeFormation`. -/
theorem pathAppElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pathAppElimRule.argShifts scope)
    (params : RawTermChildren pathAppElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ pathAppElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE residual (the DIMENSIONAL one): `pathApp`'s interval argument obligation consumes its
    -- subject at the `.dimensional` modality, where a bare variable is usable only when it resolves to a
    -- `lockCons` (the locked dimension); a non-`lockCons` variable interval argument fails.  The classifier IS
    -- `intervalTypeCell`, so the non-interval bridge is inapplicable by construction — the argument's dimensional
    -- usability is the genuine precondition supplied up-thread from the original `pathApp` cell's `usabilityHolds`.
    (argumentReductUsable : ∀ {subject : RawTerm scope},
      HasTypeUnion profile context subject intervalTypeCell →
      context.isSubjectUsableAtModality subject .dimensional = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : pathAppElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (pathAppElimRule.outputType scope args params) := by
  match args, params with
  | .childCons path (.childCons argument .childNil),
    .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have pathTyped : HasTypeUnion profile context path
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
      premisesHold _ (List.Mem.head _)
    have argumentTyped : HasTypeUnion profile context argument intervalTypeCell :=
      premisesHold _ (List.Mem.tail _ (List.Mem.head _))
    have pathClassifierFormed : UnionClassifierIsType profile context
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
      (HasTypeUnion.classifierIsPretype pathTyped wellFormed).resolveType
        (bridgeTypeCell_not_conv_intervalTypeCell carrierCode leftEndpoint rightEndpoint)
    have argumentClassifierFormed : UnionClassifierIsType profile context intervalTypeCell :=
      HasTypeUnion.classifierIsType argumentTyped wellFormed
    have carrierClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag) :=
      ⟨_, _, HasTypeUnion.universeFormation context level0 flag⟩
    have memberAfterEq : pathAppElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_pathApp () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2; rfl
    have drift := pathAppObligationsDriftUnderArgStep level0 level1 flag pathClassifierFormed
      argumentClassifierFormed carrierClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_pathApp pathAppElimRule
      (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
      level0 level1 flag rfl premisesHold childSubjectReduction drift (Conv.refl _)
      (pathAppUsabilityDischarge carrierCode leftEndpoint rightEndpoint level0 level1 flag wellFormed
        argumentReductUsable (premisesHoldUnderObligationsDrift drift childSubjectReduction premisesHold))

/-- **The `boolElim` branch (cell-spine-aligned via per-position reindexing).**  `boolElimCell` emits the spine
`(motive, thenBranch, elseBranch, scrutinee)`, so the gate's `childrenBefore` is that spine and `childStep` steps
it.  We `cases` the spine step into its four positions and, per position, construct the corresponding `args`-order
`StepChildren` (motive at `args` 0, scrutinee at `args` 1, then at `args` 2, else at `args` 3) to feed the
args-ordered `boolElimObligationsDriftUnderArgStep` / `boolElimOutputTypeDriftUnderArgStep`.  `elimGateRowReassemble`
rebuilds at `memberCell scope argsAfter`, which is DEFINITIONALLY `mkGen gen_boolElim () childrenAfter` (the
permutation `memberCell` applies to `argsAfter` reproduces the stepped spine), so `exact` closes the gate goal by
`isDefEq` — no explicit `mkGen` bridge.  The three branch-classifier formedness witnesses come from the scrutinee /
then / else obligations via `classifierIsType`; the motive obligation's universe formedness is the drift lemma's
internal `universeFormation`. -/
theorem boolElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren boolElimRule.argShifts scope)
    (params : RawTermChildren boolElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ boolElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`), reindexed per stepped spine position.
    (usabilityHolds : ∀ obligation ∈ boolElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : boolElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (boolElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))),
    .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      (HasTypeUnion.classifierIsPretype (premisesHold _ (List.Mem.head _)) wellFormed).resolveType (by
        first
          | exact boolTypeCell_not_conv_intervalTypeCell
          | exact natTypeCell_not_conv_intervalTypeCell
          | exact listTypeCell_not_conv_intervalTypeCell _
          | exact optionTypeCell_not_conv_intervalTypeCell _
          | exact eitherTypeCell_not_conv_intervalTypeCell _ _)
    have thenBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have elseBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    cases childStep with
    | here _ motiveStep =>
        exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
          childSubjectReduction
          (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
            thenBranchClassifierFormed elseBranchClassifierFormed (StepChildren.here _ motiveStep))
          (boolElimOutputTypeDriftUnderArgStep .childNil (StepChildren.here _ motiveStep))
          (usabilityHoldsUnderObligationsDrift
            (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
              thenBranchClassifierFormed elseBranchClassifierFormed (StepChildren.here _ motiveStep))
            childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
    | there _ tail1 => cases tail1 with
      | here _ thenStep =>
          exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
            childSubjectReduction
            (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
              thenBranchClassifierFormed elseBranchClassifierFormed
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
            (boolElimOutputTypeDriftUnderArgStep .childNil
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
            (usabilityHoldsUnderObligationsDrift
              (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                thenBranchClassifierFormed elseBranchClassifierFormed
                (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ thenStep))))
              childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
      | there _ tail2 => cases tail2 with
        | here _ elseStep =>
            exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
              childSubjectReduction
              (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                thenBranchClassifierFormed elseBranchClassifierFormed
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
              (boolElimOutputTypeDriftUnderArgStep .childNil
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
              (usabilityHoldsUnderObligationsDrift
                (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                  thenBranchClassifierFormed elseBranchClassifierFormed
                  (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ elseStep)))))
                childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
        | there _ tail3 => cases tail3 with
          | here _ scrutineeStep =>
              exact elimGateRowReassemble .gen_boolElim boolElimRule .childNil level0 level1 flag rfl premisesHold
                childSubjectReduction
                (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                  thenBranchClassifierFormed elseBranchClassifierFormed
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (boolElimOutputTypeDriftUnderArgStep .childNil
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (usabilityHoldsUnderObligationsDrift
                  (boolElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                    thenBranchClassifierFormed elseBranchClassifierFormed
                    (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                  childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
          | there _ emptyTailStep => cases emptyTailStep

/-- **The `optionMatch` branch** — CELL-SPINE-ALIGNED (`optionMatchCell` emits `(motive, none, some, scrutinee)` =
the rule `args`), so the gate `mkGen` bridge holds definitionally and the args-ordered drift / output-drift apply
directly.  Formedness from the scrutinee / none / some obligations. -/
theorem optionMatchGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren optionMatchElimRule.argShifts scope)
    (params : RawTermChildren optionMatchElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ optionMatchElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`) — no oracle, no interval refuter.
    (usabilityHolds : ∀ obligation ∈ optionMatchElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : optionMatchElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (optionMatchElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      (HasTypeUnion.classifierIsPretype (premisesHold _ (List.Mem.head _)) wellFormed).resolveType (by
        first
          | exact boolTypeCell_not_conv_intervalTypeCell
          | exact natTypeCell_not_conv_intervalTypeCell
          | exact listTypeCell_not_conv_intervalTypeCell _
          | exact optionTypeCell_not_conv_intervalTypeCell _
          | exact eitherTypeCell_not_conv_intervalTypeCell _ _)
    have noneBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have someBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have memberAfterEq : optionMatchElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_optionMatch () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    have drift := optionMatchObligationsDriftUnderArgStep (typeParamB := typeParamB) level0 level1 flag
      scrutineeClassifierFormed noneBranchClassifierFormed someBranchClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_optionMatch optionMatchElimRule
      (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction drift
      (optionMatchOutputTypeDriftUnderArgStep (.childCons typeParamA (.childCons typeParamB .childNil)) childStep)
      (usabilityHoldsUnderObligationsDrift drift childSubjectReduction
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem with
                | head => rfl
                | tail _ hmem => cases hmem with
                  | head => rfl
                  | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-- **The `eitherMatch` branch** — CELL-SPINE-ALIGNED (`eitherMatchCell` emits `(motive, left, right, scrutinee)` =
`args`).  Formedness from the scrutinee / left / right obligations. -/
theorem eitherMatchGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren eitherMatchElimRule.argShifts scope)
    (params : RawTermChildren eitherMatchElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ eitherMatchElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : eitherMatchElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (eitherMatchElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      (HasTypeUnion.classifierIsPretype (premisesHold _ (List.Mem.head _)) wellFormed).resolveType (by
        first
          | exact boolTypeCell_not_conv_intervalTypeCell
          | exact natTypeCell_not_conv_intervalTypeCell
          | exact listTypeCell_not_conv_intervalTypeCell _
          | exact optionTypeCell_not_conv_intervalTypeCell _
          | exact eitherTypeCell_not_conv_intervalTypeCell _ _)
    have leftBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have rightBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have memberAfterEq : eitherMatchElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_eitherMatch () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    have drift := eitherMatchObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
      leftBranchClassifierFormed rightBranchClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_eitherMatch eitherMatchElimRule
      (.childCons typeParamA (.childCons typeParamB .childNil)) level0 level1 flag rfl premisesHold
      childSubjectReduction drift
      (eitherMatchOutputTypeDriftUnderArgStep (.childCons typeParamA (.childCons typeParamB .childNil)) childStep)
      (eitherMatchUsabilityDischarge typeParamA typeParamB level0 level1 flag wellFormed
        (premisesHoldUnderObligationsDrift drift childSubjectReduction premisesHold))

/-- **The `natElim` branch** — CELL-SPINE-ALIGNED (`natElimCell` emits `(motive, zero, succ, scrutinee)` = `args`).
The binder-extended succ-branch obligation's formedness comes NOT from `classifierIsType` (its context is the
2-extended `(context.cons natType).cons motive`, whose well-formedness the gate does not carry) but from the motive
typing via `natElimDependentSuccBranchType_formed_ofMotive` — the same route the drift lemma uses internally. -/
theorem natElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natElimRule.argShifts scope) (params : RawTermChildren natElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: the before-args obligation subjects are fibrantly usable (the native `elim` arm's
    -- `usabilityHolds`, threaded from the gate); the drifted after-args subjects stay usable by step-preservation
    -- (`usabilityHoldsUnderObligationsDrift`), including the `consContextHeadConv` step branch whose context drifts.
    (usabilityHolds : ∀ obligation ∈ natElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : natElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (natElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))), .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      (HasTypeUnion.classifierIsPretype (premisesHold _ (List.Mem.head _)) wellFormed).resolveType (by
        first
          | exact boolTypeCell_not_conv_intervalTypeCell
          | exact natTypeCell_not_conv_intervalTypeCell
          | exact listTypeCell_not_conv_intervalTypeCell _
          | exact optionTypeCell_not_conv_intervalTypeCell _
          | exact eitherTypeCell_not_conv_intervalTypeCell _ _)
    have baseBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag) :=
      premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
        (natElimDependentSuccBranchType motive) :=
      ⟨level0, flag, natElimDependentSuccBranchType_formed_ofMotive context motive level0 flag motiveTyped⟩
    have memberAfterEq : natElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_natElim () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    have drift := natElimObligationsDriftUnderArgStep level0 level1 flag motiveTyped scrutineeClassifierFormed
      baseBranchClassifierFormed stepBranchClassifierFormed childSubjectReduction childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_natElim natElimRule .childNil level0 level1 flag rfl premisesHold
      childSubjectReduction drift
      (natElimOutputTypeDriftUnderArgStep .childNil childStep)
      (usabilityHoldsUnderObligationsDrift drift childSubjectReduction
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem with
                | head => rfl
                | tail _ hmem => cases hmem with
                  | head => rfl
                  | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-- **The `natRec` branch** — the `natElim` twin (same substrate; only `natRecRule` / `natRecCell` differ). -/
theorem natRecGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren natRecElimRule.argShifts scope) (params : RawTermChildren natRecElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ natRecElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: the `natElim` twin — before-args usability threaded from the gate's `usabilityHolds`,
    -- after-args usability by step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ natRecElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : natRecElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (natRecElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))), .childNil =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      (HasTypeUnion.classifierIsPretype (premisesHold _ (List.Mem.head _)) wellFormed).resolveType (by
        first
          | exact boolTypeCell_not_conv_intervalTypeCell
          | exact natTypeCell_not_conv_intervalTypeCell
          | exact listTypeCell_not_conv_intervalTypeCell _
          | exact optionTypeCell_not_conv_intervalTypeCell _
          | exact eitherTypeCell_not_conv_intervalTypeCell _ _)
    have baseBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have motiveTyped : HasTypeUnion profile (context.cons natTypeCell) motive (universeCodeCell level0 flag) :=
      premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have stepBranchClassifierFormed : UnionClassifierIsType profile ((context.cons natTypeCell).cons motive)
        (natElimDependentSuccBranchType motive) :=
      ⟨level0, flag, natElimDependentSuccBranchType_formed_ofMotive context motive level0 flag motiveTyped⟩
    have memberAfterEq : natRecElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_natRec () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3 with
            | childCons _ rest4 => cases rest4; rfl
    have drift := natRecElimObligationsDriftUnderArgStep level0 level1 flag motiveTyped scrutineeClassifierFormed
      baseBranchClassifierFormed stepBranchClassifierFormed childSubjectReduction childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_natRec natRecElimRule .childNil level0 level1 flag rfl premisesHold
      childSubjectReduction drift
      (natRecOutputTypeDriftUnderArgStep .childNil childStep)
      (usabilityHoldsUnderObligationsDrift drift childSubjectReduction
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem with
                | head => rfl
                | tail _ hmem => cases hmem with
                  | head => rfl
                  | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-- **The `idJ` branch** — CELL-SPINE-ALIGNED (`idJCell` emits `(motive, baseCase, witness)` = `args`).  Output
`idJMotiveAt motive rightEndpoint witness`; formedness from the witness / rightEndpoint / baseCase obligations. -/
theorem idJGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren idJElimRule.argShifts scope) (params : RawTermChildren idJElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ idJElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`).
    (usabilityHolds : ∀ obligation ∈ idJElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : idJElimRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (idJElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
    .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have witnessClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.head _)) wellFormed
    have rightEndpointClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have baseCaseClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    have memberAfterEq : idJElimRule.memberCell scope childrenAfter
        = RawTerm.mkGen .gen_idJ () childrenAfter := by
      cases childrenAfter with
      | childCons _ rest1 => cases rest1 with
        | childCons _ rest2 => cases rest2 with
          | childCons _ rest3 => cases rest3; rfl
    have drift := idJObligationsDriftUnderArgStep level0 level1 flag witnessClassifierFormed
      rightEndpointClassifierFormed baseCaseClassifierFormed childStep
    rw [← memberAfterEq]
    exact elimGateRowReassemble .gen_idJ idJElimRule
      (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
      level0 level1 flag rfl premisesHold childSubjectReduction drift
      (idJOutputTypeDriftUnderArgStep typeCode leftEndpoint rightEndpoint childStep)
      (usabilityHoldsUnderObligationsDrift drift childSubjectReduction
        (by intro obligation hmem
            cases hmem with
            | head => rfl
            | tail _ hmem => cases hmem with
              | head => rfl
              | tail _ hmem => cases hmem with
                | head => rfl
                | tail _ hmem => cases hmem with
                  | head => rfl
                  | tail _ hmem => cases hmem)
        premisesHold usabilityHolds)

/-- **The `listElim` branch** — CELL-SPINE-PERMUTING (the `boolElim` twin).  `listElimCell motive scrutinee
nilBranch consBranch` emits the spine `(motive, nilBranch, consBranch, scrutinee)` — scrutinee moves from `args`
position 1 to spine position 3.  So the gate's `childStep` is over the cell SPINE, not `args`, and we cannot use
the direct `mkGen` bridge.  Instead we case the spine `StepChildren` per position, identify which `args` position
stepped (the fixed permutation `spine0↦args0`, `spine1↦args2`, `spine2↦args3`, `spine3↦args1`), and feed the
args-ordered obligation / output drift at the reindexed `StepChildren`; `elimGateRowReassemble`'s `memberCell scope
argsAfter` conclusion then unifies with the goal's stepped spine by `isDefEq` (`memberCell` whnf-permutes argsAfter
into the concrete stepped spine).  The cons-branch formedness comes from the base-context obligation
(`listElimDependentConsBranchType motive elementType`), so — unlike the recursors — no `motiveTyped` is needed. -/
theorem listElimGateBranchCloses {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren listElimRule.argShifts scope)
    (params : RawTermChildren listElimRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ listElimRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (wellFormed : WfContextUnion context)
    -- ★ A1-CONJUNCT-WIRE: before-args usability threaded from the gate's `usabilityHolds`; after-args usability by
    -- step-preservation (`usabilityHoldsUnderObligationsDrift`), reindexed per stepped spine position.
    (usabilityHolds : ∀ obligation ∈ listElimRule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope}
    (memberEq : listElimRule.memberCell scope args
      = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore)
    (childStep : StepChildren childrenBefore childrenAfter) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
      Conv pinned (listElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
    .childCons elementType (.childCons resultType .childNil) =>
    injection memberEq with _scopeEq genEq payloadEq childrenEq
    subst genEq
    cases eq_of_heq payloadEq
    cases eq_of_heq childrenEq
    have scrutineeClassifierFormed :=
      (HasTypeUnion.classifierIsPretype (premisesHold _ (List.Mem.head _)) wellFormed).resolveType (by
        first
          | exact boolTypeCell_not_conv_intervalTypeCell
          | exact natTypeCell_not_conv_intervalTypeCell
          | exact listTypeCell_not_conv_intervalTypeCell _
          | exact optionTypeCell_not_conv_intervalTypeCell _
          | exact eitherTypeCell_not_conv_intervalTypeCell _ _)
    have nilBranchClassifierFormed :=
      HasTypeUnion.classifierIsType (premisesHold _ (List.Mem.tail _ (List.Mem.head _))) wellFormed
    have consBranchClassifierFormed :=
      HasTypeUnion.classifierIsType
        (premisesHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) wellFormed
    cases childStep with
    | here _ motiveStep =>
        exact elimGateRowReassemble .gen_listElim listElimRule
          (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
          childSubjectReduction
          (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
            nilBranchClassifierFormed consBranchClassifierFormed (StepChildren.here _ motiveStep))
          (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
            (StepChildren.here _ motiveStep))
          (usabilityHoldsUnderObligationsDrift
            (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
              nilBranchClassifierFormed consBranchClassifierFormed (StepChildren.here _ motiveStep))
            childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
    | there _ tail1 => cases tail1 with
      | here _ nilStep =>
          exact elimGateRowReassemble .gen_listElim listElimRule
            (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
            childSubjectReduction
            (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
              nilBranchClassifierFormed consBranchClassifierFormed
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ nilStep))))
            (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
              (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ nilStep))))
            (usabilityHoldsUnderObligationsDrift
              (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                nilBranchClassifierFormed consBranchClassifierFormed
                (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ nilStep))))
              childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
      | there _ tail2 => cases tail2 with
        | here _ consStep =>
            exact elimGateRowReassemble .gen_listElim listElimRule
              (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
              childSubjectReduction
              (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                nilBranchClassifierFormed consBranchClassifierFormed
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ consStep)))))
              (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
                (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ consStep)))))
              (usabilityHoldsUnderObligationsDrift
                (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                  nilBranchClassifierFormed consBranchClassifierFormed
                  (StepChildren.there _ (StepChildren.there _ (StepChildren.there _ (StepChildren.here _ consStep)))))
                childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
        | there _ tail3 => cases tail3 with
          | here _ scrutineeStep =>
              exact elimGateRowReassemble .gen_listElim listElimRule
                (.childCons elementType (.childCons resultType .childNil)) level0 level1 flag rfl premisesHold
                childSubjectReduction
                (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                  nilBranchClassifierFormed consBranchClassifierFormed
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (listElimOutputTypeDriftUnderArgStep (.childCons elementType (.childCons resultType .childNil))
                  (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                (usabilityHoldsUnderObligationsDrift
                  (listElimObligationsDriftUnderArgStep level0 level1 flag scrutineeClassifierFormed
                    nilBranchClassifierFormed consBranchClassifierFormed
                    (StepChildren.there _ (StepChildren.here _ scrutineeStep)))
                  childSubjectReduction
            (by intro obligation memberProof
                cases memberProof with
                | head => rfl
                | tail _ memberProof => cases memberProof with
                  | head => rfl
                  | tail _ memberProof => cases memberProof with
                    | head => rfl
                    | tail _ memberProof => cases memberProof with
                      | head => rfl
                      | tail _ memberProof => cases memberProof)
            premisesHold usabilityHolds)
          | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed

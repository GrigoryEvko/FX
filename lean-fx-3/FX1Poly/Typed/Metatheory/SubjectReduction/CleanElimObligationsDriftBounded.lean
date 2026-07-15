import FX1Poly.Typed.Metatheory.SubjectReduction.IntroObligationsDriftBounded
import FX1Poly.Axis.Term.Core.RawSize

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/CleanElimObligationsDriftBounded
    — SR-WF-TIEOFF (elim third): the FUEL-BOUNDED `ObligationsDriftBelow` for the CLEAN eliminators

The fuel-bounded twin of `CleanElimObligationsDrift.lean`.  The CLEAN eliminators — `app` / `pathApp` / `fst` /
`snd` — have NO binder-extended branches and NO motive: every obligation classifier reads only the type-index
PARAMS (which a child step leaves fixed) at the ambient context.  So when one arg steps, the obligation drift is
exactly the stepping arg's obligation getting a SUBJECT drift (the arg, a structural cell-child, so its size is
strictly below `(rule.memberCell scope args).size`), every other obligation literally unchanged, and NO classifier
drift.  This is `ObligationsDriftBelow` built entirely from the `cons` arm — `SubjectDriftBelow.stepsBelow` at the
stepping position (with the `…BelowCellSize` size witness), `SubjectDriftBelow.fixed` everywhere else, every
classifier held fixed.  No `consClassifierConv`, no `consContextHeadConv` — those are the dependent rows' province.

This file also ships the SHARED child-size witnesses (`headChildBelowCellSize` … `fourthChildBelowCellSize`) that
ALL the bounded elim drift builders reuse: a child at position k of a `mkGen`'s spine is strictly below the cell's
size, since `(mkGen generator payload children).size = children.size + 1` is DEFINITIONAL (the generator / payload
are ignored), so `child.size < (childCons … child …).size + 1` is defeq to `child.size < (rule.memberCell scope
args).size` once `memberCell scope args` reduces to its `mkGen` spine.

## Zero-axiom

`cases` on the (mutual-inductive) `StepChildren` + `SubjectDriftBelow` / `ObligationsDriftBelow` constructors +
the `RawSize` `size_lt_childCons_*` / `Nat.lt_trans` / `Nat.lt_succ_self` bound arithmetic.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Shared child-size witnesses — a child at spine position k is strictly below its `mkGen` cell's size

`(RawTerm.mkGen generator payload children).size` is DEFINITIONALLY `children.size + 1`, so a bound `child.size <
(childCons … child …).size + 1` is defeq to `child.size < (rule.memberCell scope args).size` once `memberCell scope
args` reduces to its `mkGen` spine.  These four cover the head through fourth child positions every clean / recursor
/ dependent-match row needs.

The shift of each child position is an EXPLICIT leading argument (`firstShift` / …): a clean-row child sits at
`scope + 0` (defeq `scope`), a recursor / dependent motive at `scope + 1` or `scope + 2`; passing the shift
explicitly lets the child term (declared at `RawTerm scope` / `RawTerm (scope + k)`) defeq-check against the
helper's `RawTerm (scope + firstShift)` instead of leaving Lean to solve the non-pattern `scope =?= scope + ?s`. -/

/-- The head child is strictly below its parent cell's size (`childCons … + 1`). -/
theorem headChildBelowCellSize {scope : Nat} (firstShift : Nat) {restShifts : List Nat}
    (head : RawTerm (scope + firstShift)) (tail : RawTermChildren restShifts scope) :
    head.size < (RawTermChildren.childCons head tail).size + 1 :=
  Nat.lt_trans (RawTermChildren.size_lt_childCons_head head tail) (Nat.lt_succ_self _)

/-- The second child is strictly below its grandparent cell's size. -/
theorem secondChildBelowCellSize {scope : Nat} (firstShift secondShift : Nat) {restShifts : List Nat}
    (first : RawTerm (scope + firstShift)) (second : RawTerm (scope + secondShift))
    (tail : RawTermChildren restShifts scope) :
    second.size < (RawTermChildren.childCons first (.childCons second tail)).size + 1 :=
  Nat.lt_trans
    (Nat.lt_trans (RawTermChildren.size_lt_childCons_head second tail)
      (RawTermChildren.size_lt_childCons_tail first _))
    (Nat.lt_succ_self _)

/-- The third child is strictly below its great-grandparent cell's size. -/
theorem thirdChildBelowCellSize {scope : Nat} (firstShift secondShift thirdShift : Nat) {restShifts : List Nat}
    (first : RawTerm (scope + firstShift)) (second : RawTerm (scope + secondShift))
    (third : RawTerm (scope + thirdShift)) (tail : RawTermChildren restShifts scope) :
    third.size < (RawTermChildren.childCons first (.childCons second (.childCons third tail))).size + 1 :=
  Nat.lt_trans
    (Nat.lt_trans
      (Nat.lt_trans (RawTermChildren.size_lt_childCons_head third tail)
        (RawTermChildren.size_lt_childCons_tail second _))
      (RawTermChildren.size_lt_childCons_tail first _))
    (Nat.lt_succ_self _)

/-- The fourth child is strictly below its enclosing cell's size. -/
theorem fourthChildBelowCellSize {scope : Nat} (firstShift secondShift thirdShift fourthShift : Nat)
    {restShifts : List Nat}
    (first : RawTerm (scope + firstShift)) (second : RawTerm (scope + secondShift))
    (third : RawTerm (scope + thirdShift)) (fourth : RawTerm (scope + fourthShift))
    (tail : RawTermChildren restShifts scope) :
    fourth.size
      < (RawTermChildren.childCons first
          (.childCons second (.childCons third (.childCons fourth tail)))).size + 1 :=
  Nat.lt_trans
    (Nat.lt_trans
      (Nat.lt_trans
        (Nat.lt_trans (RawTermChildren.size_lt_childCons_head fourth tail)
          (RawTermChildren.size_lt_childCons_tail third _))
        (RawTermChildren.size_lt_childCons_tail second _))
      (RawTermChildren.size_lt_childCons_tail first _))
    (Nat.lt_succ_self _)

/-! ## The four clean rows -/

/-- **`app`'s fuel-bounded obligation drift under one arg step.**  Bounded twin of
`appObligationsDriftUnderArgStep`: when `function` or `argument` steps, only that obligation's subject drifts (a
`SubjectDriftBelow.stepsBelow` whose source is strictly below `(appElimRule.memberCell scope args).size`), the
other obligation is `SubjectDriftBelow.fixed`, and neither classifier (`piTyCode` / `domainCode`, both fixed
params) moves. -/
theorem appObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {function argument : RawTerm scope} {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (functionClassifierFormed : UnionClassifierIsType profile context (piTyCodeCell domainCode codomainCode))
    (argumentClassifierFormed : UnionClassifierIsType profile context domainCode)
    {argsAfter : RawTermChildren [0, 0] scope}
    (childStep : StepChildren
      (.childCons function (.childCons argument .childNil) : RawTermChildren [0, 0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (appElimRule.memberCell scope (.childCons function (.childCons argument .childNil))).size
      (appElimRule.obligations scope context
        (.childCons function (.childCons argument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag)
      (appElimRule.obligations scope context argsAfter
        (.childCons domainCode (.childCons codomainCode .childNil)) level0 level1 flag) := by
  cases childStep with
  | here _ functionStep =>
      exact ObligationsDriftBelow.cons (.stepsBelow functionStep (headChildBelowCellSize 0 function _))
        functionClassifierFormed
        (ObligationsDriftBelow.cons (.fixed argument) argumentClassifierFormed ObligationsDriftBelow.nil)
  | there _ tailStep =>
      cases tailStep with
      | here _ argumentStep =>
          exact ObligationsDriftBelow.cons (.fixed function) functionClassifierFormed
            (ObligationsDriftBelow.cons (.stepsBelow argumentStep (secondChildBelowCellSize 0 0 function argument _))
              argumentClassifierFormed ObligationsDriftBelow.nil)
      | there _ emptyTailStep => cases emptyTailStep

/-- **`pathApp`'s fuel-bounded obligation drift under one arg step.**  Three obligations — `path` at the bridge
type, `argument` at the interval type, `carrierCode` (a PARAM) at its universe code.  When `path` or `argument`
steps only that obligation's subject drifts; the `carrierCode` obligation and every classifier stay fixed. -/
theorem pathAppObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (pathClassifierFormed : UnionClassifierIsType profile context
      (bridgeTypeCell carrierCode leftEndpoint rightEndpoint))
    (argumentClassifierFormed : UnionClassifierIsType profile context intervalTypeCell)
    (carrierClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag))
    {argsAfter : RawTermChildren [0, 0] scope}
    (childStep : StepChildren
      (.childCons path (.childCons argument .childNil) : RawTermChildren [0, 0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (pathAppElimRule.memberCell scope (.childCons path (.childCons argument .childNil))).size
      (pathAppElimRule.obligations scope context
        (.childCons path (.childCons argument .childNil))
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag)
      (pathAppElimRule.obligations scope context argsAfter
        (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
        level0 level1 flag) := by
  cases childStep with
  | here _ pathStep =>
      exact ObligationsDriftBelow.cons (.stepsBelow pathStep (headChildBelowCellSize 0 path _)) pathClassifierFormed
        (ObligationsDriftBelow.cons (.fixed argument) argumentClassifierFormed
          (ObligationsDriftBelow.cons (.fixed carrierCode) carrierClassifierFormed ObligationsDriftBelow.nil))
  | there _ tailStep =>
      cases tailStep with
      | here _ argumentStep =>
          exact ObligationsDriftBelow.cons (.fixed path) pathClassifierFormed
            (ObligationsDriftBelow.cons (.stepsBelow argumentStep (secondChildBelowCellSize 0 0 path argument _))
              argumentClassifierFormed
              (ObligationsDriftBelow.cons (.fixed carrierCode) carrierClassifierFormed ObligationsDriftBelow.nil))
      | there _ emptyTailStep => cases emptyTailStep

/-- **`fst`'s fuel-bounded obligation drift under one arg step.**  `fst` eliminates a single child `pairTerm` (at
the product type) plus the self-certifying `firstType` formedness obligation (a PARAM).  When `pairTerm` steps its
subject drifts; the `firstType` obligation stays fixed. -/
theorem fstObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm firstType secondType : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (pairClassifierFormed : UnionClassifierIsType profile context (productTypeCell firstType secondType))
    (firstTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag))
    {argsAfter : RawTermChildren [0] scope}
    (childStep : StepChildren (.childCons pairTerm .childNil : RawTermChildren [0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (fstElimRule.memberCell scope (.childCons pairTerm .childNil)).size
      (fstElimRule.obligations scope context (.childCons pairTerm .childNil)
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag)
      (fstElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag) := by
  cases childStep with
  | here _ pairStep =>
      exact ObligationsDriftBelow.cons (.stepsBelow pairStep (headChildBelowCellSize 0 pairTerm _)) pairClassifierFormed
        (ObligationsDriftBelow.cons (.fixed firstType) firstTypeClassifierFormed ObligationsDriftBelow.nil)
  | there _ emptyTailStep => cases emptyTailStep

/-- **`snd`'s fuel-bounded obligation drift under one arg step** — the `fst` twin (the self-certifying second
obligation pins `secondType`, also a fixed param). -/
theorem sndObligationsDriftUnderArgStepBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm firstType secondType : RawTerm scope}
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (pairClassifierFormed : UnionClassifierIsType profile context (productTypeCell firstType secondType))
    (secondTypeClassifierFormed : UnionClassifierIsType profile context (universeCodeCell level0 flag))
    {argsAfter : RawTermChildren [0] scope}
    (childStep : StepChildren (.childCons pairTerm .childNil : RawTermChildren [0] scope) argsAfter) :
    ObligationsDriftBelow profile
      (sndElimRule.memberCell scope (.childCons pairTerm .childNil)).size
      (sndElimRule.obligations scope context (.childCons pairTerm .childNil)
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag)
      (sndElimRule.obligations scope context argsAfter
        (.childCons firstType (.childCons secondType .childNil)) level0 level1 flag) := by
  cases childStep with
  | here _ pairStep =>
      exact ObligationsDriftBelow.cons (.stepsBelow pairStep (headChildBelowCellSize 0 pairTerm _)) pairClassifierFormed
        (ObligationsDriftBelow.cons (.fixed secondType) secondTypeClassifierFormed ObligationsDriftBelow.nil)
  | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed

import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CarrierAwareFlatFormationMember
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # FX1Poly/Typed/CarrierAwareFlatFormationRows
    — the product / either / equiv carrier-aware flat formation FT rows over the native obligation list + FREE
      levels (TYTAB-4 step 4)

`CarrierAwareFlatFormationMember.lean` discharged the generic carrier-aware flat member at FIXED component levels.
This file lifts it to the shape the native `formationFundamental` premise demands: the subject is the generic
`mkGen generator payload children`, the obligation hypotheses arrive as the single `∀ obligation ∈
flatFormationObligations …` list, and the level list is FREE (so the output universe is `universeFormerOutput
scope levels flag = Type@(lmaxAll levels)`).

## The positional free-`levels` dispatch

Unlike the cumulative binder spine, `flatFormationObligations` is POSITIONAL: each child is zipped with the
corresponding level, surplus children forced to `Type@0`.  So after the two-child spine the obligation-level pairs
are:

  * `levels = firstLevel :: secondLevel :: _` → `(firstLevel, secondLevel)` (the real row);
  * `levels = [singleLevel]` → `(singleLevel, Type@0)` (only the SECOND child is forced to `lzero`);
  * `levels = []` → `(Type@0, Type@0)` (both forced).

The single-element case is the genuinely new shape (the cumulative rows forced BOTH levels to `lzero` there): the
member lands at `Type@(lmaxAll [singleLevel, lzero])`, whose denote is `levelMax (denote singleLevel) 0` — lifted to
the output `Type@singleLevel` via `levelMax_zero_right`.  The dispatch is factored once into the generic
spine row `fundamentalCarrierAwareFlatSpineRowAtBoundedSucc`; the three per-generator wrappers just match the
two-child spine and pin the combinator (`pairLike` / `coproductLike` / `equivLike`), the subject collapsing
definitionally (`combinator.cell first second = mkGen generator () children`, payload eta).

## Zero-axiom verification

`levelMax_zero_right` is two `rfl` clauses; the spine row is a three-way `match` on `levels` feeding the member +
`fundamentalConclusion_universeCumulative` with elementary `lmaxFold` / `levelMax` bounds; the wrappers are a
`match` + `show` + `exact`.  No induction (the inductions live in the support layer), no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- `levelMax value 0 = value` — the right-zero collapse, two `rfl` clauses mirroring `LevelExpr.levelMax`
(`levelMax 0 0 = 0` and `levelMax (n+1) 0 = n+1`).  Needed for the positional single-level flat case, where the
forced-`lzero` second component leaves the member at `levelMax (denote singleLevel) 0`, equal to the output level
`denote singleLevel`. -/
theorem levelMax_zero_right : ∀ (value : Nat), LevelExpr.levelMax value 0 = value
  | 0 => rfl
  | _ + 1 => rfl

/-- **The generic carrier-aware flat formation FT spine row (TYTAB-4 step 4).**  From the native obligation-list
IHs over `flatFormationObligations` (the two children at their positional levels) under a FREE `levels`, the cell
`combinator.cell firstCode secondCode` (product / either / equiv) is a bound-reducible member of the free output
universe `Type@(lmaxAll levels)`.  Dispatches the three positional level shapes, lands the carrier-aware member, and
lifts to the free output universe by `fundamentalConclusion_universeCumulative`. -/
theorem fundamentalCarrierAwareFlatSpineRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope) (combinator : CarrierCombinator)
    {firstCode secondCode : RawTerm scope} {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag
          (.childCons firstCode (.childCons secondCode .childNil) : RawTermChildren [0, 0] scope) levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (combinator.cell firstCode secondCode)
      (universeCodeCell (lmaxAll levels) flag) := by
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
      (fundamentalCarrierAwareFlatMemberAtBoundedSucc env bound context combinator firstLevel secondLevel
        flag firstIH secondIH)
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
      (fundamentalCarrierAwareFlatMemberAtBoundedSucc env bound context combinator singleLevel
        LevelExpr.lzero flag firstIH secondIH)
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
      (fundamentalCarrierAwareFlatMemberAtBoundedSucc env bound context combinator LevelExpr.lzero
        LevelExpr.lzero flag firstIH secondIH)
      (by rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]; exact Nat.zero_le _)
      boundPositive
      substitution envReducible

/-- **The product carrier-aware flat formation FT row.**  `mkGen gen_productCode payload children` is a
bound-reducible member of `Type@(lmaxAll levels)`; the two-child spine collapses to `pairLike.cell` and the spine
row closes. -/
theorem fundamentalProductFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_productCode.payload scope}
    {children : RawTermChildren Generator.gen_productCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_productCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons first (.childCons second .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (CarrierCombinator.pairLike.cell first second) (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalCarrierAwareFlatSpineRowAtBoundedSucc env bound context CarrierCombinator.pairLike
      levelsBelowBound boundPositive obligationsFundamental

/-- **The either carrier-aware flat formation FT row.**  `mkGen gen_eitherCode payload children` is a
bound-reducible member of `Type@(lmaxAll levels)`; collapses to `coproductLike.cell`. -/
theorem fundamentalEitherFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_eitherCode.payload scope}
    {children : RawTermChildren Generator.gen_eitherCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_eitherCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons first (.childCons second .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (CarrierCombinator.coproductLike.cell first second) (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalCarrierAwareFlatSpineRowAtBoundedSucc env bound context CarrierCombinator.coproductLike
      levelsBelowBound boundPositive obligationsFundamental

/-- **The equiv carrier-aware flat formation FT row.**  `mkGen gen_equivCode payload children` is a bound-reducible
member of `Type@(lmaxAll levels)`; collapses to `equivLike.cell`.  This is the equivalence code becoming a typed
formation capability through the native bundle FT — the bounded twin of `equivCodeFundamentalFromCarriers`. -/
theorem fundamentalEquivFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_equivCode.payload scope}
    {children : RawTermChildren Generator.gen_equivCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ flatFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_equivCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons first (.childCons second .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (CarrierCombinator.equivLike.cell first second) (universeCodeCell (lmaxAll levels) flag)
    exact fundamentalCarrierAwareFlatSpineRowAtBoundedSucc env bound context CarrierCombinator.equivLike
      levelsBelowBound boundPositive obligationsFundamental

end FX1Poly.Typed

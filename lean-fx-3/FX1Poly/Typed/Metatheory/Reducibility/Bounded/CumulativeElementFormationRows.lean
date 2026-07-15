import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedGenFormationListFromTelescope
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedGenFormationOptionFromTelescope
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedTelescopeConsSucc
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeFreeLevelsSupport
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # FX1Poly/Typed/CumulativeElementFormationRows
    — the List / Option cumulative formation FT members + rows over FREE levels (TYTAB-4 step 4)

The element-shape cumulative type-formers (List / Option, both single-child spine `[0]`) are the
NON-binder-crossing half of the cumulative formation sub-family.  Unlike Π/Σ, their one child sits at the ambient
scope (no codomain under a binder), so the telescope bridge is the trivial single-child one: no variable-0
inhabitant, no argument lift — the element obligation IH plus a `nil` tail.

## The single-child bridge + members

`oneChildFormationTelescopeAtBoundedSucc` re-assembles the element obligation IH into the one-child telescope the
shipped `fundamentalGenFormation{List,Option}FromTelescopeAtBoundedSucc` arms consume (`fundamentalTelescopeCons`
with a `nil` tail).  The members compose it with those arms, landing `mkGen gen_{list,option}Code () (childCons
element childNil)` as a member of `Type@(lmaxAll [elementLevel])`.

## The rows (free `levels`)

`fundamentalCumulative{List,Option}RowAtBoundedSucc` lift the members to the native premise shape: generic
`mkGen generator payload children` subject, the single obligation-list IH, FREE `levels` (output
`Type@(lmaxAll levels)`).  After the single-child spine, `cumulativeFormationObligations` reduces — on `levels` — to
the single element obligation at `levels.head` (or forced `Type@0` when `levels = []`).  Two-way dispatch: the
element IH lands the member at `Type@(lmaxAll [OBL_EL])`, lifted to the free output `Type@(lmaxAll levels)` by
`fundamentalConclusion_universeCumulative` (`denote_le_lmaxFold` / `denote_lmaxFold_lt` for the real case;
`Nat.le_refl` / `boundPositive` for the forced-`lzero` empty case).

## Zero-axiom verification

`match` on the spine + two-way `match` on `levels`, member application + the cumulativity lift.  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- **The single-child formation telescope bridge (TYTAB-4 step 4).**  From the element obligation IH, the one
child forms the List/Option telescope at the former's output level `denote (lmaxAll [elementLevel]) env`.  The
trivial single-child re-assembly: `fundamentalTelescopeConsAtBoundedSucc` over the element IH with a `nil` tail —
no binder crossing, no argument lift (the element sits at the ambient scope). -/
theorem oneChildFormationTelescopeAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {element : RawTerm scope} (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementFundamental :
      FundamentalConclusionAtBoundedSucc env bound context element (universeCodeCell elementLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        TelescopeReducibleAtBounded env bound (LevelExpr.denote (lmaxAll [elementLevel]) env) flag 0 1
          substitution [elementLevel] (.childCons element .childNil) := by
  intro _targetScope substitution envReducible
  exact fundamentalTelescopeConsAtBoundedSucc env bound _ envReducible elementFundamental
    (fun _argument _argumentMember => fundamentalTelescopeNilAtBounded env bound _)

/-- **The List cumulative formation FT member (TYTAB-4 step 4).**  From the element obligation IH,
`mkGen gen_listCode () (childCons element childNil)` is a bound-reducible member of
`Type@(lmaxAll [elementLevel])`.  The single-child bridge fed to the shipped List from-telescope arm. -/
theorem fundamentalCumulativeListMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {element : RawTerm scope} (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementFundamental :
      FundamentalConclusionAtBoundedSucc env bound context element (universeCodeCell elementLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_listCode () (.childCons element .childNil))
      (universeCodeCell (lmaxAll [elementLevel]) flag) :=
  fundamentalGenFormationListFromTelescopeAtBoundedSucc env bound context elementLevel flag
    (oneChildFormationTelescopeAtBoundedSucc env bound context elementLevel flag elementFundamental)

/-- **The Option cumulative formation FT member (TYTAB-4 step 4).**  The Option twin of
`fundamentalCumulativeListMemberAtBoundedSucc`, feeding the shipped Option from-telescope arm. -/
theorem fundamentalCumulativeOptionMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {element : RawTerm scope} (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementFundamental :
      FundamentalConclusionAtBoundedSucc env bound context element (universeCodeCell elementLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_optionCode () (.childCons element .childNil))
      (universeCodeCell (lmaxAll [elementLevel]) flag) :=
  fundamentalGenFormationOptionFromTelescopeAtBoundedSucc env bound context elementLevel flag
    (oneChildFormationTelescopeAtBoundedSucc env bound context elementLevel flag elementFundamental)

/-- **The List cumulative formation FT row (TYTAB-4 step 4).**  From the native obligation-list IH over
`cumulativeFormationObligations` under a FREE `levels`, the cell `mkGen gen_listCode payload children` is a
bound-reducible member of the free output universe `universeFormerOutput scope levels flag = Type@(lmaxAll
levels)`.  Two-way `levels` dispatch (the real element level, or the forced `Type@0` empty case), lands the member
and lifts to the free output universe. -/
theorem fundamentalCumulativeListRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_listCode.payload scope}
    {children : RawTermChildren Generator.gen_listCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ cumulativeFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_listCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons element .childNil =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_listCode () (.childCons element .childNil)) (universeCodeCell (lmaxAll levels) flag)
    intro targetScope substitution envReducible
    match levels with
    | elementLevel :: restLevels =>
      have elementIH : FundamentalConclusionAtBoundedSucc env bound context element
          (universeCodeCell elementLevel flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := element,
            classifier := universeCodeCell elementLevel flag } (List.Mem.head _)
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [elementLevel]) (lmaxAll (elementLevel :: restLevels)) flag
        (fundamentalCumulativeListMemberAtBoundedSucc env bound context elementLevel flag elementIH)
        (denote_le_lmaxFold env restLevels elementLevel)
        (denote_lmaxFold_lt env bound restLevels elementLevel
          (levelsBelowBound elementLevel (List.Mem.head _))
          (fun levelExpr levelMem => levelsBelowBound levelExpr (List.Mem.tail _ levelMem)))
        substitution envReducible
    | [] =>
      have elementIH : FundamentalConclusionAtBoundedSucc env bound context element
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := element,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [LevelExpr.lzero]) (lmaxAll []) flag
        (fundamentalCumulativeListMemberAtBoundedSucc env bound context LevelExpr.lzero flag elementIH)
        (Nat.le_refl _)
        boundPositive
        substitution envReducible

/-- **The Option cumulative formation FT row (TYTAB-4 step 4).**  The Option twin of
`fundamentalCumulativeListRowAtBoundedSucc`: identical two-way free-`levels` dispatch, landing
`fundamentalCumulativeOptionMemberAtBoundedSucc`. -/
theorem fundamentalCumulativeOptionRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_optionCode.payload scope}
    {children : RawTermChildren Generator.gen_optionCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ cumulativeFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_optionCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons element .childNil =>
    show FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_optionCode () (.childCons element .childNil)) (universeCodeCell (lmaxAll levels) flag)
    intro targetScope substitution envReducible
    match levels with
    | elementLevel :: restLevels =>
      have elementIH : FundamentalConclusionAtBoundedSucc env bound context element
          (universeCodeCell elementLevel flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := element,
            classifier := universeCodeCell elementLevel flag } (List.Mem.head _)
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [elementLevel]) (lmaxAll (elementLevel :: restLevels)) flag
        (fundamentalCumulativeOptionMemberAtBoundedSucc env bound context elementLevel flag elementIH)
        (denote_le_lmaxFold env restLevels elementLevel)
        (denote_lmaxFold_lt env bound restLevels elementLevel
          (levelsBelowBound elementLevel (List.Mem.head _))
          (fun levelExpr levelMem => levelsBelowBound levelExpr (List.Mem.tail _ levelMem)))
        substitution envReducible
    | [] =>
      have elementIH : FundamentalConclusionAtBoundedSucc env bound context element
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := element,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [LevelExpr.lzero]) (lmaxAll []) flag
        (fundamentalCumulativeOptionMemberAtBoundedSucc env bound context LevelExpr.lzero flag elementIH)
        (Nat.le_refl _)
        boundPositive
        substitution envReducible

end FX1Poly.Typed

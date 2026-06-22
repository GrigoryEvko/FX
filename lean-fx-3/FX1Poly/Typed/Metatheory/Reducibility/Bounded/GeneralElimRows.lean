import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge

/-! # FX1Poly/Typed/GeneralElimRows
    — the general (non-data) eliminator FT members (TYTAB-4 step 4, the elim side's `app` case)

The eliminators whose member witness is a SHIPPED bounded-member engine rather than a data-eliminator
reducibility argument.  `app` (function application) is exactly the bounded Π-elimination engine
`fundamentalPiElimAtBoundedSucc` (DenoteKeyedBoundedAssemblyBridge): from the function's fundamental
conclusion at its Π code and the argument's at the domain, the application is a bound-reducible member of the
instantiated codomain `subst0 codomainCode argument` — exactly the `app` row's output.

So the `app` elim row is a pure wiring of `fundamentalPiElimAtBoundedSucc`: extract the two obligation IHs
(function @ `piTyCodeCell domainCode codomainCode`, argument @ `domainCode`), feed the engine, and close (its
conclusion is definitionally the row's goal, `memberCell` / `outputType` reducing to `appCell` / `subst0`).
The union-table restatement of the grown-engine piElim recursor arm.

## Zero-axiom verification

`fundamentalPiElimAtBoundedSucc` (the application member engine) + the propext-clean `List.Mem` obligation
witnesses.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The `gen_app` elim FT member: `f(a)` is a bound-reducible member of `B[a]` given `f : Π(x:A). B` and
`a : A`.  Output type `subst0 codomainCode argument` is the application's instantiated codomain; the member
witness is the shipped `fundamentalPiElimAtBoundedSucc` Π-elimination engine, fed the function and argument
obligation IHs — the union-table restatement of the grown-engine piElim recursor arm. -/
theorem fundamentalAppElimRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren appElimRule.argShifts scope}
    {params : RawTermChildren appElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ appElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (appElimRule.memberCell scope args)
      (appElimRule.outputType scope args params) := by
  match args, params with
  | .childCons function (.childCons argument .childNil),
    .childCons domainCode (.childCons codomainCode .childNil) =>
    have functionFundamental :
        FundamentalConclusionAtBoundedSucc env bound context function
          (piTyCodeCell domainCode codomainCode) :=
      premisesFundamental
        { scope := scope, context := context, subject := function,
          classifier := piTyCodeCell domainCode codomainCode }
        (List.Mem.head _)
    have argumentFundamental :
        FundamentalConclusionAtBoundedSucc env bound context argument domainCode :=
      premisesFundamental
        { scope := scope, context := context, subject := argument, classifier := domainCode }
        (List.Mem.tail _ (List.Mem.head _))
    -- Type-ascribe the Π-elimination engine's conclusion (folded `FundamentalConclusionAtBoundedSucc` head),
    -- then close into the closing-substitution form so the goal's `memberCell` / `outputType` reduce to
    -- `appCell` / `subst0` (match-iota).
    have applicationMember :
        FundamentalConclusionAtBoundedSucc env bound context (appCell function argument)
          (RawTerm.subst0 codomainCode argument) :=
      fundamentalPiElimAtBoundedSucc env bound context functionFundamental argumentFundamental
    intro _targetScope substitution envReducible
    exact applicationMember substitution envReducible

end FX1Poly.Typed

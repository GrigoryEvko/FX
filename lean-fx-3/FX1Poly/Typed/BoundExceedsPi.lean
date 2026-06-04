import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.BoundExceedsDesc

/-! # FX1Poly/Typed/BoundExceedsPi
    — the per-derivation universe-level budget for the GROWN engine (BFT-12a)

`BoundExceedsDesc.lean` defines `BoundExceeds` over the FORMATION engine (`HasTypeDesc`), whose `universeFormation`
leaf carries the per-term `belowBound` fuel.  To discharge the bounded grown fundamental theorem (BFT-12c) at a
SINGLE fixed bound, the grown engine needs its own budget `BoundExceedsPi` over `HasTypeDescPi` (mutual with
`BoundExceedsPiTelescope` over `DescTelescopePi`).

## Why the grown budget carries the embedded `BoundExceeds` (not a derivable gate)

The grown engine has NO `universeFormation` constructor — every universe level it touches is gate-EXTRACTED from a
reducible member produced by an IH (the conv/piIntro/genFormationPi arms of BFT-6 read `belowBound` off a member,
never off a budget).  The ONLY place a level must be SUPPLIED is the embedded formation derivation reached through
`ofFormation`.  That budget cannot be derived at a fixed bound: `BoundExceeds.existsBound` gives a per-derivation
bound, and `monotoneInBound` only lifts a budget UP — so a fixed bound chosen for the whole grown derivation cannot
be guaranteed to exceed an arbitrary embedded formation sub-derivation unless that sub-budget is CARRIED.  Hence the
`ofFormation` constructor carries `BoundExceeds env bound formationTyped`; every other constructor merely threads
sub-`BoundExceedsPi`s (conv/piIntro/piElim) or the telescope budget (genFormationPi).  There is no `belowBound`
constructor here — the fuel is entirely inside the carried `BoundExceeds`.

## The discharge plan (BFT-12b/12c)

`monotoneInBound` + `existsBound` for `BoundExceedsPi` mirror `BoundExceedsDischarge.lean` exactly (term-mode match
on the budget for monotonicity with the `conv` `converts` pinned in the pattern; `HasTypeDescPi.rec` for existence
with SUM bounds via `Nat.le_add_*`, the `ofFormation` arm delegating to `BoundExceeds.existsBound` on the embedded
derivation).  Then `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c) runs `BoundExceedsPi.rec`, its `ofFormation`
arm extracting the named embedded `BoundExceeds` to feed `HasTypeDesc.fundamentalAtBoundedSucc` (BFT-11), every
other arm mirroring BFT-6.

## Zero-axiom verification

A mutual inductive `Prop` family indexed by `HasTypeDescPi` / `DescTelescopePi` derivations; strictly positive
(`BoundExceedsPi` only in premises, `BoundExceeds` positively in `ofFormation`).  Inductives introduce no axioms
(checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/- **The per-derivation universe-level budget for the grown engine (indexed inductive `Prop`).**  `BoundExceedsPi
env bound d` threads the budget down every grown-engine constructor to the embedded formation budgets it reaches
through `ofFormation`; it carries NO `belowBound` of its own (the grown engine has no universe leaf).  Mutual with
`BoundExceedsPiTelescope`. -/
mutual
inductive BoundExceedsPi {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    {scope : Nat} → {context : TypingContext profile scope} → {subject classifier : RawTerm scope} →
    HasTypeDescPi profile context subject classifier → Prop where
  | ofFormation {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      {formationTyped : HasTypeDesc profile context subject classifier}
      (formationBudget : BoundExceeds env bound formationTyped) :
      BoundExceedsPi env bound (HasTypeDescPi.ofFormation formationTyped)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope} (levelExpr : LevelExpr) (flag : UniverseFlag)
      {typed : HasTypeDescPi profile context subject classifier} {converts : Conv classifier reclassifier}
      {reclassifierTyped : HasTypeDescPi profile context reclassifier (universeCodeCell levelExpr flag)}
      (subjectBudget : BoundExceedsPi env bound typed)
      (reclassifierBudget : BoundExceedsPi env bound reclassifierTyped) :
      BoundExceedsPi env bound (HasTypeDescPi.conv levelExpr flag typed converts reclassifierTyped)
  | piIntro {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      {domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag)}
      {codomainTyped : HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)}
      {bodyTyped : HasTypeDescPi profile (context.cons domainCode) body codomainCode}
      (domainBudget : BoundExceedsPi env bound domainTyped)
      (codomainBudget : BoundExceedsPi env bound codomainTyped)
      (bodyBudget : BoundExceedsPi env bound bodyTyped) :
      BoundExceedsPi env bound
        (HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped)
  | piElim {scope : Nat} {context : TypingContext profile scope}
      {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {functionTyped : HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode)}
      {argumentTyped : HasTypeDescPi profile context argument domainCode}
      (functionBudget : BoundExceedsPi env bound functionTyped)
      (argumentBudget : BoundExceedsPi env bound argumentTyped) :
      BoundExceedsPi env bound (HasTypeDescPi.piElim functionTyped argumentTyped)
  | genFormationPi {scope : Nat} (context : TypingContext profile scope) (generator : Generator)
      (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc)
      (isFormation : typingRuleDescOf generator = some rule)
      {premises : DescTelescopePi profile (currentDepth := 0) context levels flag children}
      (premisesBudget : BoundExceedsPiTelescope env bound premises) :
      BoundExceedsPi env bound
        (HasTypeDescPi.genFormationPi context generator payload children levels flag rule isFormation premises)
inductive BoundExceedsPiTelescope {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    {baseScope currentDepth : Nat} → {binderShifts : List Nat} →
    {context : TypingContext profile (baseScope + currentDepth)} → {levels : List LevelExpr} →
    {flag : UniverseFlag} → {children : RawTermChildren binderShifts baseScope} →
    DescTelescopePi profile context levels flag children → Prop where
  | nil {baseScope currentDepth : Nat} (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      BoundExceedsPiTelescope env bound (DescTelescopePi.nil context flag)
  | cons {baseScope currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth)) (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      {headTyped : HasTypeDescPi profile context head (universeCodeCell headLevel flag)}
      {restTyped : DescTelescopePi profile (currentDepth := currentDepth + 1) (context.cons head)
        restLevels flag rest}
      (headBudget : BoundExceedsPi env bound headTyped)
      (restBudget : BoundExceedsPiTelescope env bound restTyped) :
      BoundExceedsPiTelescope env bound
        (DescTelescopePi.cons context head headLevel restLevels flag rest headTyped restTyped)
end

end FX1Poly.Typed

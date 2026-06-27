import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # FX1Poly/Typed/DimensionLockBreakerRejection — the SR-breaker fails the lock AT THE REAL RULE TABLE

`DimensionLockAccessibility` proves the ABSTRACT subject-level certificate
(`lockedDimensionSubjectNotUsableFibrantly`: the locked dimension `var 0` fails `isSubjectUsableAtModality`
at the fibrant modality).  This file CONNECTS that certificate to the actual `pairIntroRule` of the shipped
typing-table bundle: the canonical subject-reduction breaker — the duplicating bridge body
`pair (var 0) (var 0)`, where `var 0` is the dimension bound by the affine lock — has, among the obligations
the REAL `pairIntroRule` demands, a FIRST obligation whose subject is the locked `var 0` consumed at a
FIBRANT use-position, and that obligation fails the use-site usability conjunct.

So once the conjunct-wire (`A1-CONJUNCT-WIRE`) makes the three table arms require
`obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true` on every
obligation, this `false` obligation makes `pair (var 0) (var 0)` UNTYPEABLE under the lock — the pathLam
subject-reduction is then STRUCTURAL (by the context's `lockCons`), with no beta-fragile occurrence count.
This is the concrete rule-table witness underpinning `A1-SR-STRUCTURAL`: the mechanism is checked against the
shipped `pairIntroRule`, not merely the abstract `isSubjectUsableAtModality` predicate.

## Zero-axiom

The obligations list of `pairIntroRule` applied to concrete `.childCons` children reduces definitionally to a
head obligation whose three fields (`context`, `subject = variableCell 0`, `modality = .fibrant` default) feed
`lockedDimensionSubjectNotUsableFibrantly` directly.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The duplicating bridge body is rejected by the lock at the SHIPPED `pairIntroRule`.**  Under the affine
dimension lock `restContext.lockCons dimensionType`, the SR-breaker `pair (var 0) (var 0)` — a fibrant
constructor applied twice to the locked dimension `var 0` — has, among the obligations `pairIntroRule` demands,
one whose `subject` is the locked `var 0` at the `.fibrant` use-position and whose use-site usability conjunct
is `false`.  Once `A1-CONJUNCT-WIRE` makes the intro arm require that conjunct on every obligation, this `false`
entry makes the breaker untypeable structurally — the count-free, beta-stable pathLam subject reduction.  The
concrete rule-table instantiation of `lockedDimensionSubjectNotUsableFibrantly`. -/
theorem pairDuplicatingDimensionBodyRejectedByLock {profile : PolyProfile} {predScope : Nat}
    (restContext : TypingContext profile predScope) (dimensionType : RawTerm predScope)
    (typeParam0 typeParam1 : RawTerm (predScope + 1)) (level0 level1 : LevelExpr) (flag : UniverseFlag) :
    ∃ obligation ∈ pairIntroRule.obligations (predScope + 1) (restContext.lockCons dimensionType)
        (.childCons (variableCell ⟨0, Nat.zero_lt_succ predScope⟩)
          (.childCons (variableCell ⟨0, Nat.zero_lt_succ predScope⟩) .childNil))
        (.childCons typeParam0 (.childCons typeParam1 .childNil))
        level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = false := by
  refine ⟨_, List.Mem.head _, ?_⟩
  exact lockedDimensionSubjectNotUsableFibrantly restContext dimensionType (Nat.zero_lt_succ predScope)

end FX1Poly.Typed

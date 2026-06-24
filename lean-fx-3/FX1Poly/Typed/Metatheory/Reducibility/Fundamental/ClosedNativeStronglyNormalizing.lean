import FX1Poly.Typed.Metatheory.Reducibility.Fundamental.BoundedUnionFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.ClosedBoundedReducibleMember
import FX1Poly.Core.Metatheory.Normalization.Core.StronglyNormalizingSubst

/-! # FX1Poly/Typed/ClosedNativeStronglyNormalizing
    — the NATIVE closed-term strong-normalization reflection, conditional on the three table-arm FTs (TYTAB-4 step 5)

The native-union twin of `HasTypeDescPi.closedStronglyNormalizing` (`Corpus/Smoke/ClosedStronglyNormalizing.lean`):
every CLOSED union derivation `HasTypeUnionOver bundle .empty subject classifier` has a strongly-normalizing
`subject` — given the three table-arm fundamental theorems (`formationFundamental` / `introFundamental` /
`elimFundamental`) over the bundle.  This is **step 5 of the TYTAB-4 native-SN construction** (the closed reflection
that turns the budget-conditional native fundamental theorem into native SN), and it directly supplies gate 1
(`nativeStronglyNormalizing : IsStronglyNormalizing subject`) of the consistency leg of TYTAB-2-FT (#1697,
`EmptyTypeConsistencyNativeUnion.coreFragmentConsistencyFromElimCongruenceCloser`).

## The assembly (mirrors the grown closed reflection exactly)

The grown path was `closedBoundedReducibleMember` (BFT-13) → `stronglyNormalizing_of_memberAtBoundedSucc` (scope+1
bounded CR1) → `StepStar.stronglyNormalizing_of_subst` (reflect through the closing weakening) = SN-043-closed.  The
native path swaps the two engine-specific pieces for their union analogues, keeping the two member→SN bridges
verbatim (both are production-agnostic — they read SN off the member, never how it was produced):

  1. `BoundExceedsUnion.existsBound d` (TYTAB-4 step 2) supplies a concrete `bound` and budget.
  2. `HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms (fun _ => 0) bound … d budget` (TYTAB-4 step 3),
     instantiated at the unique closing substitution `Fin.elim0 : RawTermSubst 0 1` with the vacuous empty-context
     environment witness `ReducibleEnvAtBounded.empty`, gives a bound-reducible member of the weakened classifier.
  3. `stronglyNormalizing_of_memberAtBoundedSucc` reads SN of `subst Fin.elim0 subject` (scope 1) off the member.
  4. `StepStar.stronglyNormalizing_of_subst` reflects that to `IsStronglyNormalizing subject` (scope 0).

## Why the three premises are `∀ env bound`-polymorphic

Step 3's dispatch is conditional on the three table-arm FTs at a FIXED `(env, bound)`, but closed reflection's
`bound` is existentially produced by `existsBound` after the derivation is in hand.  So the three premises are
threaded here as `∀ env bound, <table-arm FT at that (env, bound)>`.  The `formationFundamental` and
`introFundamental` premises discharge cleanly at the kernel bundle — their generic FT arms hold at every level
bound (the formation arm and the seventeen intro bounded-member rows are shipped).

## The `succContractumTerminates` residue IS dischargeable from scrutinee MEMBERSHIP (the combine family closes it)

An earlier note here claimed the bare `elimFundamental` premise was UNREACHABLE for the recursive eliminators
because `fundamentalNatElimRowAtBoundedSucc` (and the `natRec` / `listElim` twins) thread a contractum-termination
residue `succContractumTerminates` (`∀ predecessor, SN predecessor → SN (succ-ι contractum)`) that looks
unsatisfiable at the open / arbitrary level — the contractum embeds a raw `natElimCellSpine` at an arbitrary
strongly-normalizing predecessor, and raw recursors are not globally SN.  That claim was too pessimistic: the
quantifier is the bug, not the goal.  The bare elim premise hands its scrutinee obligation an IH that is
scrutinee MEMBERSHIP in the data candidate, not bare SN.  A member of `dataTaitCandidate IsNatStructured`
(resp. `IsListStructured`) reduces to a STRUCTURED value whose ι-firing predecessor / tail is itself a member
reaching a STRUCTURALLY-SMALLER value — so the recursive call's SN is a structural numeral / list descent, never
an arbitrary SN term.  That is exactly what the combine family proves:

  * `natElimCellSpine_isStronglyNormalizing_of_structuredMember` and its `natRec` twin
    (`Core/Eliminators/Nat/NatElimStructuredMemberStrongNormalization.lean`),
  * `listElimCellSpine_isStronglyNormalizing_of_structuredMember`
    (`Core/Eliminators/List/ListElimStructuredMemberStrongNormalization.lean`).

Each derives whole-cell SN from the scrutinee MEMBER: a 4-fold `Acc StepSuccessor` inner engine peels the spine
(CR2 keeps every reduct a member, confluence keeps it reaching the normal target), and a structural induction on
`IsNatStructured` / `IsListStructured` supplies the ι-firing discharge from the OUTER IH at the smaller value —
vacuous at the zero / nil / neutral leaves.  So the residue `succContractumTerminates` is REPLACED by a weaker,
dischargeable `succBranchSubstClosed` quantified over MEMBER predecessors, satisfiable at the
fundamental-theorem level where the branches are reducible (not merely SN).

What remains is WIRING, not a missing theorem: the dependent members and the bounded fundamental rows must route
through the combine.  The genuine friction is that the combine is SN-valued (its `succBranchSubstClosed` premise
is `SN recursiveResult → SN (subst …)`) while the dependent members live in the membership world (their existing
substitution-closure is `member recursiveResult → member (subst …)`); the two flavours do not interconvert, so the
membership-aware dispatch and the per-eliminator residue drop are a deliberate multi-step consolidation, tracked
on the TYTAB-2-FT consistency leg.  When that lands, this composition is unconditional native closed SN on the
recursive fragment too, and `coreFragmentConsistencyFromElimCongruenceCloser` becomes conditional on only the
eliminator-congruence closer.

## Zero-axiom verification

A composition of `BoundExceedsUnion.existsBound` + `fundamentalAtBoundedSuccFromTableArms` + the two shipped
member→SN bridges + `Fin.elim0` + `ReducibleEnvAtBounded.empty`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **★ NATIVE closed-term strong normalization, conditional on the three table-arm FTs (TYTAB-4 step 5).**  Every
closed union derivation (`HasTypeUnionOver bundle .empty subject classifier`) has a strongly-normalizing `subject`,
given the `formationRule` / `intro` / `elim` table-arm fundamental theorems (threaded `∀ env bound`-polymorphic, the
shape TYTAB-4 step 4 produces at the kernel bundle).  The native twin of `HasTypeDescPi.closedStronglyNormalizing`:
budget (`BoundExceedsUnion.existsBound`) → native FT dispatch (`fundamentalAtBoundedSuccFromTableArms`) → closed
bound-reducible member → scope+1 bounded CR1 → SN-reflection through the closing weakening.  Supplies gate 1
(`nativeStronglyNormalizing`) of native consistency (#1697); unconditional once the three premises land. -/
theorem HasTypeUnionOver.closedStronglyNormalizingFromTableArms {bundle : TypingTableBundle} {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (formationFundamental :
      ∀ (env : Nat → Nat) (bound : Nat)
        {scope : Nat} {context : TypingContext profile scope} {generator : Generator}
        {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
        {rule : FormationRule} {levels : List LevelExpr} {carrier : RawTerm scope} {level : LevelExpr}
        {flag : UniverseFlag},
        bundle.formationRule generator = some rule →
        (∀ levelExpr, levelExpr ∈ level :: levels → LevelExpr.denote levelExpr env < bound) →
        (∀ obligation (_hmem : obligation ∈ rule.obligations profile context children levels carrier level flag),
          FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
            obligation.classifier) →
        FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
          (rule.outputType scope levels level flag))
    (introFundamental :
      ∀ (env : Nat → Nat) (bound : Nat)
        {scope : Nat} {context : TypingContext profile scope} {generator : Generator} {rule : IntroRule}
        {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
        {level0 level1 : LevelExpr} {flag : UniverseFlag},
        bundle.intro generator = some rule →
        rule.sideCondition scope args →
        (∀ obligation (_hmem : obligation ∈ rule.obligations scope context args params level0 level1 flag),
          FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
            obligation.classifier) →
        FundamentalConclusionAtBoundedSucc env bound context (rule.memberCell scope args)
          (rule.outputType scope args params))
    (elimFundamental :
      ∀ (env : Nat → Nat) (bound : Nat)
        {scope : Nat} {context : TypingContext profile scope} {generator : Generator} {rule : ElimRule}
        {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
        {level0 level1 : LevelExpr} {flag : UniverseFlag},
        bundle.elim generator = some rule →
        (∀ obligation (_hmem : obligation ∈ rule.obligations scope context args params level0 level1 flag),
          FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
            obligation.classifier) →
        FundamentalConclusionAtBoundedSucc env bound context (rule.memberCell scope args)
          (rule.outputType scope args params))
    (d : HasTypeUnionOver bundle profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨bound, budget⟩ := BoundExceedsUnion.existsBound (env := fun _ => 0) d
  have member :
      IsReducibleMemberAtBounded (fun _ => 0) bound
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) classifier)
        (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject) :=
    HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms (fun _ => 0) bound
      (formationFundamental (fun _ => 0) bound) (introFundamental (fun _ => 0) bound)
      (elimFundamental (fun _ => 0) bound) d budget
      (targetScope := 0) (Fin.elim0 : RawTermSubst 0 1)
      (ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1))
  exact StepStar.stronglyNormalizing_of_subst (Fin.elim0 : RawTermSubst 0 1) subject
    (stronglyNormalizing_of_memberAtBoundedSucc member)

end FX1Poly.Typed

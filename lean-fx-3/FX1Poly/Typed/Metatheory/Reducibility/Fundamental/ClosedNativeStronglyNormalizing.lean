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

## The `elimFundamental` premise is NOT dischargeable in this bare shape for the RECURSIVE eliminators (honest caveat)

The bare `elimFundamental` premise asks for the elim conclusion from the obligation IHs ALONE, at an OPEN scope
with a closing substitution.  For the recursive eliminators that is unreachable: `fundamentalNatElimRowAtBounded\
Succ` (and the `natRec` / `listElim` twins) produce the conclusion only by ALSO threading `succContractum\
Terminates`, a contractum-termination residue (`∀ predecessor, SN predecessor → SN (succ-ι contractum)`) that is
genuinely UNSATISFIABLE at this open / arbitrary level: the contractum embeds a raw `natElimCellSpine` at an
arbitrary strongly-normalizing predecessor, and raw recursors are not globally SN (so no closing-substitution and
no IH supplies it).  Even the data-canonical normal-form dispatch `natElimDataTaitMember` cannot drop it — the
residue feeds the WHOLE-cell SN (CR1) the dispatch consumes as input, strictly more than the numeral coverage of
the branch's substitution-closure.  So THIS composition is the closed-SN route for the NON-recursive fragment
only; it is NOT the route to unconditional native SN for the recursive eliminators.

The recursive eliminators' real route is the closed-DERIVATION-recursive SN that discharges the residue per node
via closed canonicity: a closed scrutinee typed at `Nat` reduces to a NUMERAL (`NatUnionReducesToNumeral`), and a
`natElim` at a numeral has a strongly-normalizing contractum by structural induction on the numeral
(`natElimComputesToNumeral` — the predecessor is structurally smaller, so the recursive call's SN is the
structural IH, not the over-general residue).  Those pieces are shipped; the closed-recursive assembly over the
union derivation is the open recursor-SN keystone.  When it lands, this composition is unconditional native closed
SN on that fragment, and `coreFragmentConsistencyFromElimCongruenceCloser` becomes conditional on only the
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

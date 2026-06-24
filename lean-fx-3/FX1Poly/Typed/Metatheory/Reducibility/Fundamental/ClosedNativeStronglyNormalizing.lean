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

## The recursive-eliminator whole-cell SN residue is UNSATISFIABLE as an SN-of-branches obligation (honest caveat)

For the recursive eliminators (`natElim` / `natRec` / `listElim`) the bare `elimFundamental` premise is unreachable,
and for a SHARP reason.  The dispatch's whole-cell SN ingredient (the CR1 the head-expansion candidate consumes) is
supplied by `natElim_isStronglyNormalizing_of_strongly_normalizing_branches`, which demands a contractum-termination
residue of the form

    succContractumTerminates : ∀ currentMotive currentSucc predecessor currentZero,
      SN predecessor → SN (subst (cons (natElimCellSpine currentMotive predecessor currentZero currentSucc)
                                       (singleton predecessor)) currentSucc)

quantified over ARBITRARY branches — no reducibility, not even SN, on `currentZero` / `currentSucc`.  That statement
is universally FALSE.  Counterexample: `currentZero := lam (app (var 0) (var 0))` (a normal form, hence SN),
`predecessor := natZeroCell` (SN, so the premise holds), `currentSucc := app (var 0) (var 0)`.  The recursor cell
ι-reduces (zero-ι) to `currentZero`, so the substituted contractum reduces to `app currentZero currentZero =
(λx. x x) (λx. x x) = Ω`, which is NOT SN.  The root cause is the textbook fact that SUBSTITUTION DOES NOT PRESERVE
SN: putting an SN term into an SN term can create a divergent redex.  Recursor whole-cell SN at an OPEN scrutinee is
therefore not derivable from SN-of-branches at all — it genuinely requires the branches to be REDUCIBLE (Tait
members), the property closed under the substitution the ι-rule performs.

An earlier revision of this note (and a `*CellSpine_isStronglyNormalizing_of_structuredMember` "combine" family in
`Core/Eliminators/{Nat,List}/*StructuredMemberStrongNormalization.lean`) claimed the residue was discharged from
scrutinee MEMBERSHIP via a structural descent on the value the scrutinee reaches.  The structural-descent SKELETON
is sound, but the combine's `succBranchSubstClosed` premise repeats exactly the same defect — it quantifies
`recursiveResult` and `currentSucc` over arbitrary SN terms, so the identical `(λx. x x)(λx. x x)` counterexample
refutes it.  The combine family is therefore vacuously conditional on a false premise and is currently DEAD
(referenced only by the zero-axiom audit gates, wired into no live proof); it is a retirement candidate.

The principled route — the genuine open content of #1697 gate 1 — keeps the structural descent but feeds it the
MEMBER-valued contractum closure (the `succBranchSubstClosed` of `natElimDependentReducibleMember`,
`member predecessor → member (recursor cell at predecessor) → member contractum`) together with an outer induction
that yields the recursor cell's MEMBERSHIP (not bare SN) at the structurally-smaller predecessor.  Membership ⟹ SN
then discharges CR1 with NO separate SN obligation — the same shape the non-recursive eliminators already use
(reach-conditioned member payloads), which is why the non-recursive fragment is unconditional.  Concretely this
re-architects `natElim_isStronglyNormalizing_of_strongly_normalizing_branches` to consume reducibility rather than
SN-of-branches.  Until it lands, the recursor `elimFundamental` premise stays open and
`coreFragmentConsistencyFromElimCongruenceCloser` is conditional on it for the recursive fragment.

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

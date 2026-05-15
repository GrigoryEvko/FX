import LeanFX2.Reducibility.Basic
import LeanFX2.Term.Rename

/-! # LeanFX2.Reducibility.Kripke.Predicate — step-indexed Kripke Tait

Direct Ty-recursive Kripke `ReducibleK` is rejected by Lean 4 v4.29.1
(the arrow closure's `ReducibleK (domainType.rename rho) ...` is not
a structural sub-Ty call; `termination_by`-based well-founded
recursion is banned by GatesCore line 51).

This file uses **step-indexed Kripke Tait**: recurse on a `Nat`
step counter, with each unfolding decreasing the step.  Lean
accepts Nat-structural recursion trivially.

## Encoding discipline

The naive single-match `ReducibleK : Nat → Ty → ... → Prop` over a
multi-arity (Nat × Ty) scrutinee leaks `propext` per
`feedback_lean_match_arity_axioms` memory.  This file factors the
match so Nat is outer (single-arg recursion) and Ty is inner via
`ReducibleKBody`.

## Reference

- Ahmed 2006, "Step-indexed syntactic logical relations"
- Krebbers et al (Iris), step-indexed predicates for separation logic
-/

namespace LeanFX2

/-- Inner per-Ty arm function: given a fixed step number for sub-calls
plus a Ty and a typed term, returns the per-Ty closure proposition.

This is the workhorse — split out from the outer Nat-scrutinee
to avoid the multi-arity match propext leak. -/
def ReducibleKBody {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (subCallPredicate :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (subTy : Ty level targetScope) {subRaw : RawTerm targetScope},
        Term targetCtx subTy subRaw → Prop)
    : ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  -- Closed-leaf arms.
  | Ty.unit, _, term => Term.isStronglyNormalizing term
  | Ty.bool, _, term => Term.isStronglyNormalizing term
  | Ty.nat, _, term => Term.isStronglyNormalizing term
  | Ty.empty, _, term => Term.isStronglyNormalizing term
  | Ty.interval, _, term => Term.isStronglyNormalizing term
  | Ty.universe _ _, _, term => Term.isStronglyNormalizing term
  | Ty.tyVar _, _, term => Term.isStronglyNormalizing term
  -- Arrow with Kripke closure invoking subCallPredicate at subCallStep.
  | Ty.arrow domainType codomainType, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.rename rho) argumentRaw),
        subCallPredicate (domainType.rename rho) argumentTerm →
        subCallPredicate (codomainType.rename rho)
                   (Term.app (Term.rename termRenaming functionTerm)
                             argumentTerm)
  -- Dependent Π closure: SN of the function plus a Kripke closure
  -- that takes any future world's reducible argument at the renamed
  -- domain to a reducible `appPi`-application at the substituted
  -- renamed codomain.  Mirrors `Ty.arrow`'s closure modulo the
  -- dependent codomain (substitutes argument into `codomainType.rename
  -- rho.lift` via `Ty.subst0`).
  | Ty.piTy domainType codomainType, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.rename rho) argumentRaw),
        subCallPredicate (domainType.rename rho) argumentTerm →
        subCallPredicate
          ((codomainType.rename rho.lift).subst0
            (domainType.rename rho) argumentRaw)
          (Term.appPi (Term.rename termRenaming functionTerm) argumentTerm)
  -- Dependent Σ closure: SN of the pair plus reducibility of both
  -- projections (`Term.fst` / `Term.snd`) in every future world.  The
  -- second projection lands at the substituted renamed `secondType`
  -- (with `RawTerm.fst (rawPair.rename rho)` in the substituent
  -- slot), matching the typed kernel's `Term.snd` result type.
  | Ty.sigmaTy firstType secondType, _, pairTerm =>
      Term.isStronglyNormalizing pairTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (firstType.rename rho)
          (Term.fst (Term.rename termRenaming pairTerm)) ∧
        subCallPredicate
          ((secondType.rename rho.lift).subst0
            (firstType.rename rho)
            (RawTerm.fst (pairTerm.toRaw.rename rho)))
          (Term.snd (Term.rename termRenaming pairTerm))
  -- HoTT identity type — Kripke closure via the `Term.idJ` eliminator.
  -- A reducible identity witness produces a reducible result at any
  -- motive when paired with a reducible base case in every future
  -- world.  Mirrors the standard induction-on-identity Tait closure;
  -- the motive is universally quantified because the motiveType is
  -- unrelated to the identity-type structure (J's elimination
  -- principle).
  | Ty.id _ _ _, _, witnessTerm =>
      Term.isStronglyNormalizing witnessTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {motiveType : Ty level targetScope}
        {baseRaw : RawTerm targetScope}
        (baseCase : Term targetCtx motiveType baseRaw),
        subCallPredicate motiveType baseCase →
        subCallPredicate motiveType
          (Term.idJ baseCase (Term.rename termRenaming witnessTerm))
  -- List closure: SN of the scrutinee plus the elimination clause —
  -- in every future world, for every motive `motiveType` and every
  -- reducible nil-/cons-branch, the `Term.listElim` application is
  -- reducible at `motiveType`.  This is the standard Tait closure
  -- shape for a finitary inductive type: parameterized over the
  -- motive and discharging via the inductive eliminator.
  | Ty.listType elementType, _, scrutineeTerm =>
      Term.isStronglyNormalizing scrutineeTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        (motiveType : Ty level targetScope)
        {nilRaw consRaw : RawTerm targetScope}
        (nilBranch : Term targetCtx motiveType nilRaw)
        (consBranch :
          Term targetCtx
            (Ty.arrow (elementType.rename rho)
              (Ty.arrow (Ty.listType (elementType.rename rho)) motiveType))
            consRaw),
        subCallPredicate motiveType nilBranch →
        subCallPredicate
          (Ty.arrow (elementType.rename rho)
            (Ty.arrow (Ty.listType (elementType.rename rho)) motiveType))
          consBranch →
        subCallPredicate motiveType
          (Term.listElim (Term.rename termRenaming scrutineeTerm)
            nilBranch consBranch)
  -- Option closure: same shape as list with the `Term.optionMatch`
  -- eliminator and none-/some-branches.
  | Ty.optionType elementType, _, scrutineeTerm =>
      Term.isStronglyNormalizing scrutineeTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        (motiveType : Ty level targetScope)
        {noneRaw someRaw : RawTerm targetScope}
        (noneBranch : Term targetCtx motiveType noneRaw)
        (someBranch :
          Term targetCtx (Ty.arrow (elementType.rename rho) motiveType)
            someRaw),
        subCallPredicate motiveType noneBranch →
        subCallPredicate
          (Ty.arrow (elementType.rename rho) motiveType) someBranch →
        subCallPredicate motiveType
          (Term.optionMatch (Term.rename termRenaming scrutineeTerm)
            noneBranch someBranch)
  -- Either closure: same shape as list/option with the
  -- `Term.eitherMatch` eliminator and left/right branches.
  | Ty.eitherType leftType rightType, _, scrutineeTerm =>
      Term.isStronglyNormalizing scrutineeTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        (motiveType : Ty level targetScope)
        {leftRaw rightRaw : RawTerm targetScope}
        (leftBranch :
          Term targetCtx (Ty.arrow (leftType.rename rho) motiveType) leftRaw)
        (rightBranch :
          Term targetCtx (Ty.arrow (rightType.rename rho) motiveType) rightRaw),
        subCallPredicate
          (Ty.arrow (leftType.rename rho) motiveType) leftBranch →
        subCallPredicate
          (Ty.arrow (rightType.rename rho) motiveType) rightBranch →
        subCallPredicate motiveType
          (Term.eitherMatch (Term.rename termRenaming scrutineeTerm)
            leftBranch rightBranch)
  -- Cubical path type — Kripke closure via the `Term.pathApp`
  -- eliminator.  Applying a path to a reducible interval value
  -- produces a reducible result at the carrier.  The closure clause
  -- is conditional on `mode = Mode.univalent` because `Term.pathApp`
  -- requires that discipline; under non-univalent modes the clause is
  -- vacuously satisfiable (no inhabitant of the hypothesis exists)
  -- and the SN component still constrains the term.  Note that
  -- endpoint specialisation (`pathApp p i0 ⟶ source`, `pathApp p i1
  -- ⟶ target`) lives at the Step level — the type-level closure says
  -- only that the result sits at `carrierType.rename rho`.
  | Ty.path carrierType _ _, _, pathTerm =>
      Term.isStronglyNormalizing pathTerm ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent)
        {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {intervalRaw : RawTerm targetScope}
        (intervalTerm : Term targetCtx Ty.interval intervalRaw),
        subCallPredicate Ty.interval intervalTerm →
        subCallPredicate (carrierType.rename rho)
          (Term.pathApp modeIsUnivalent
            (Term.rename termRenaming pathTerm) intervalTerm)
  -- Cubical glue type — Kripke closure via the `Term.glueElim`
  -- destructor.  A reducible glue value projects to a reducible base
  -- value at the base carrier.  Same `modeIsUnivalent` discipline as
  -- the path arm.
  | Ty.glue baseType _, _, gluedTerm =>
      Term.isStronglyNormalizing gluedTerm ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent)
        {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (baseType.rename rho)
          (Term.glueElim modeIsUnivalent
            (Term.rename termRenaming gluedTerm))
  -- Observational equality — Kripke closure via the `Term.oeqJ`
  -- eliminator.  Mirrors `Ty.id`'s closure (same J-style shape,
  -- distinct raw vocabulary marking the oeq path through reduction
  -- targets).
  | Ty.oeq _ _ _, _, witnessTerm =>
      Term.isStronglyNormalizing witnessTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {motiveType : Ty level targetScope}
        {baseRaw : RawTerm targetScope}
        (baseCase : Term targetCtx motiveType baseRaw),
        subCallPredicate motiveType baseCase →
        subCallPredicate motiveType
          (Term.oeqJ baseCase (Term.rename termRenaming witnessTerm))
  -- Strict (definitional) identity — Kripke closure via
  -- `Term.idStrictRec`.  Same J-shape as `Ty.id` modulo the
  -- strict-mode side condition `modeIsStrict : mode = Mode.strict`
  -- demanded by the eliminator.
  | Ty.idStrict _ _ _, _, witnessTerm =>
      Term.isStronglyNormalizing witnessTerm ∧
      ∀ (modeIsStrict : mode = Mode.strict)
        {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {motiveType : Ty level targetScope}
        {baseRaw : RawTerm targetScope}
        (baseCase : Term targetCtx motiveType baseRaw),
        subCallPredicate motiveType baseCase →
        subCallPredicate motiveType
          (Term.idStrictRec modeIsStrict baseCase
            (Term.rename termRenaming witnessTerm))
  -- Type equivalence — Kripke closure via `Term.equivApply`.  Applying
  -- a packaged equivalence to a reducible source-carrier value
  -- produces a reducible target-carrier value.  Binary application
  -- shape mirrors `Ty.arrow`'s closure modulo the carrier-swap
  -- (`leftTy → rightTy` versus `domainType → codomainType`).
  | Ty.equiv leftTy rightTy, _, equivTerm =>
      Term.isStronglyNormalizing equivTerm ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho)
        {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (leftTy.rename rho) argumentRaw),
        subCallPredicate (leftTy.rename rho) argumentTerm →
        subCallPredicate (rightTy.rename rho)
          (Term.equivApply (Term.rename termRenaming equivTerm) argumentTerm)
  -- Refinement Kripke closure: SN of the refined value plus Tait
  -- closure under the `refineElim` eliminator, which extracts the
  -- base value at `baseType` (the predicate witness is forgotten).
  -- In every future world the renamed `refineElim` produces a
  -- reducible base-typed term.
  | Ty.refine baseType _, _, refinedValue =>
      Term.isStronglyNormalizing refinedValue ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (baseType.rename rho)
          (Term.refineElim (Term.rename termRenaming refinedValue))
  -- Record Kripke closure: SN of the record plus closure under the
  -- `recordProj` eliminator at the single-field type.  Multi-field
  -- records compose via nested singletons; the closure scales by
  -- recursion on `Ty.record`.
  | Ty.record singleFieldType, _, recordValue =>
      Term.isStronglyNormalizing recordValue ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (singleFieldType.rename rho)
          (Term.recordProj (Term.rename termRenaming recordValue))
  -- Codata Kripke closure: SN of the codata value plus closure under
  -- the `codataDest` eliminator, which observes one output at
  -- `outputType`.  In every future world the renamed `codataDest`
  -- produces a reducible output-typed term.
  | Ty.codata _ outputType, _, codataValue =>
      Term.isStronglyNormalizing codataValue ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (outputType.rename rho)
          (Term.codataDest (Term.rename termRenaming codataValue))
  -- Session Kripke closure: SN of the channel plus closure under the
  -- `sessionRecv` eliminator.  The current typed kernel preserves the
  -- session carrier across `sessionRecv` (full protocol-state
  -- advancement lives at the Sessions layer per the constructor doc),
  -- so the closure shape is same-type reducibility preservation.
  -- The dual `sessionSend` is not added to the closure clause because
  -- it requires a payload of arbitrary `payloadType` — that produces a
  -- type-quantification cycle.  Same-type preservation under
  -- `sessionRecv` is the operationally-meaningful Tait closure here.
  | Ty.session protocolStep, _, channelValue =>
      Term.isStronglyNormalizing channelValue ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (Ty.session (protocolStep.rename rho))
          (Term.sessionRecv (Term.rename termRenaming channelValue))
  -- Effect Kripke closure: SN of the effect-typed value plus
  -- closure under uniform renaming.  No typed eliminator over
  -- `Ty.effect` accepts an arbitrary effectful value at the carrier
  -- type (the Effects-layer `effectPerform` is schematic in its
  -- `OperationSignature` / `CanPerform` witnesses), so the closure
  -- drops the eliminator application and reduces to renaming-
  -- stability — in any future world the renamed effect value is
  -- reducible at the renamed `Ty.effect` head.
  | Ty.effect carrierType effectTag, _, effectValue =>
      Term.isStronglyNormalizing effectValue ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (Ty.effect (carrierType.rename rho) (effectTag.rename rho))
          (Term.rename termRenaming effectValue)
  -- Modal Kripke closure: SN of the modal value plus closure under
  -- the `modElim` eliminator.  Per Layer 1's modal scaffolding
  -- (Term.lean lines 295-300), `modElim` preserves the carrying type
  -- — when the input has type `Ty.modal modalityTag innerType`,
  -- `modElim` returns the same type with the raw wrapped in
  -- `RawTerm.modElim`.  The closure shape is therefore same-type
  -- preservation across all 8 modalities (box/diamond/flat/sharp/
  -- ghost/cap/later/clock) — uniform dispatch is correct because the
  -- typed eliminator does not yet differentiate modalities.  When
  -- Layer 6 lands and `modElim` becomes mode-changing, this closure
  -- specializes per-modality.
  | Ty.modal modalityTag innerType, _, modalValue =>
      Term.isStronglyNormalizing modalValue ∧
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        {rho : RawRenaming scope targetScope}
        (termRenaming : TermRenaming context targetCtx rho),
        subCallPredicate (Ty.modal modalityTag (innerType.rename rho))
          (Term.modElim (Term.rename termRenaming modalValue))

/-- **Kripke Tait reducibility candidate**, step-indexed.

`ReducibleK 0 ty t` holds trivially.  At step `n+1`, dispatch to
`ReducibleKBody` with sub-calls at step `n` quantified through
the `subCallPredicate` parameter.

Recursion is on `Nat` only; Lean accepts this trivially. -/
def ReducibleK {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : Nat → ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  | 0 => fun _ {_} _ => True
  | stepCount + 1 =>
      ReducibleKBody
        (fun {_} {targetCtx'} subTy {_} subTerm =>
          @ReducibleK _ _ _ targetCtx' stepCount subTy _ subTerm)

end LeanFX2

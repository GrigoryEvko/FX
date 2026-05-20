import LeanFX2.Term.StrengtheningImage.TotalOnWeakenTypeCodesMisc

/-! # Term/StrengtheningImage/TotalOnWeakenCastCore

Total-on-weaken cast-heavy wrappers for snd, funextRefl, appPi, and pair.
-/

namespace LeanFX2

namespace Term

/-! ## Wave I: Eq.mpr-blocked ctor totality.

Seven constructors have a type-equality cast in their `Term.rename` arm
(via `Ty.subst0_rename_commute.symm ▸ ...`), so `Term.weaken nt (Term.<ctor> ...)`
produces an Eq.mpr-wrapped term.  This wrapping blocks the standard
`unfold + split` template because the dispatcher's pattern-match cannot
see the constructor head through the cast.

Resolution: ship per-ctor `weaken_<ctor>_eq` rewrite lemmas that expose
the structural shape (each is `rfl`), then use `strengthenTyped?_isSome_castInvariant`
to discharge the cast and reduce to the un-cast form, which the
standard template handles.

Three ctors have OUTER casts (appPi, snd, funextRefl) — the cast wraps
the whole Term.snd/Term.appPi/Term.funextRefl head.
One ctor (boolElim) has OUTER + INNER casts.
Three ctors (pair, equivIntroHet, oeqFunext) have INNER casts on
specific subterms (secondValue / leftInv+rightInv / pointwiseProof). -/

/-- `Term.weaken` arm reshape for `Term.snd`.

The rename arm of `Term.snd` wraps the constructed `Term.snd (rename pairTerm)`
in `(Ty.subst0_rename_commute ...).symm ▸ ...` to align the result type
with the expected post-rename shape.  This lemma exposes that wrapping
explicitly for use in totality proofs.

Proved by `rfl` because `Term.weaken := Term.rename ...` is `@[reducible]`
and the rename arm's body normalises to the cast-wrapped form. -/
theorem weaken_snd_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (newType : Ty level scope)
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.weaken newType (Term.snd pairTerm) =
      ((Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd) :
       Term (context.cons newType)
         ((secondType.subst0 firstType pairRaw.fst).rename RawRenaming.weaken)
         (pairRaw.rename RawRenaming.weaken).snd) := by
  rfl

/-- 1-IH non-binder totality through Eq.mpr cast: `Term.snd`.

The Eq.mpr-blocked variant uses `weaken_snd_unfolds` + cast-invariance to
reduce to the standard `Term.snd` arm of the dispatcher.  Body shape
mirrors `isTotalOnWeaken_fst` after the cast discharge. -/
theorem isTotalOnWeaken_snd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH : IsTotalOnWeaken pairTerm) :
    IsTotalOnWeaken (Term.snd pairTerm) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd)).isSome by
    rw [weaken_snd_unfolds newType pairTerm]
    show ((Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd)).strengthenTyped?.isSome = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstType :=
        Ty.strengthen?_weaken firstType
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some secondType := by
          have := Ty.partialStrengthen?_rename_some secondType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [secondSuccess] at secondFails
        cases secondFails
    · split
      · next pairRecurse =>
          exfalso
          have totHyp := pairIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType pairTerm))) = true :=
            pairRecurse ▸ totHyp
          cases this
      · rfl

/-- `Term.weaken` arm reshape for `Term.funextRefl`.

The rename arm wraps in `(funextReflType_rename ...).symm ▸ ...` to
align the result Ty index.  Proved by `rfl`. -/
theorem weaken_funextRefl_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    Term.weaken newType
        (Term.funextRefl (context := context) domainType codomainType applyRaw) =
      ((funextReflType_rename RawRenaming.weaken domainType codomainType applyRaw).symm ▸
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift)))) :
       Term (context.cons newType)
         ((funextReflType domainType codomainType applyRaw).rename RawRenaming.weaken)
         (RawTerm.lam (RawTerm.refl applyRaw)).weaken) := by
  rfl

/-- 0-IH parametric atomic totality through Eq.mpr cast: `Term.funextRefl`.

`Term.funextRefl` carries two Ty payloads + one RawTerm at scope+1
applyRaw.  No Term IH.  The rename arm has an outer Eq.mpr wrapping the
constructor; we discharge via cast invariance + the standard atomic
template (domain success, codomain success, apply success, rfl). -/
theorem isTotalOnWeaken_funextRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextRefl (context := context)
      domainType codomainType applyRaw) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift))))).isSome by
    rw [weaken_funextRefl_unfolds newType domainType codomainType applyRaw]
    show ((funextReflType_rename RawRenaming.weaken
        domainType codomainType applyRaw).symm ▸
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift))))).strengthenTyped?.isSome = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back
            (fun position => rfl)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyFails =>
          exfalso
          have applySuccess :
              (applyRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyRaw := by
            have := RawTerm.partialStrengthen?_rename_some applyRaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applySuccess] at applyFails
          cases applyFails
      · rfl

/-- `Term.weaken` arm reshape for `Term.appPi`.

The rename arm wraps in `(Ty.subst0_rename_commute ...).symm ▸ ...` to
align the result Ty index.  Proved by `rfl`. -/
theorem weaken_appPi_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (newType : Ty level scope)
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term.weaken newType (Term.appPi functionTerm argumentTerm) =
      ((Ty.subst0_rename_commute codomainType domainType argumentRaw
          RawRenaming.weaken).symm ▸
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))) :
       Term (context.cons newType)
         ((codomainType.subst0 domainType argumentRaw).rename RawRenaming.weaken)
         (RawTerm.app functionRaw argumentRaw).weaken) := by
  rfl

/-- 2-IH non-binder totality through Eq.mpr cast: `Term.appPi`.

Dependent Π application — codomain at scope+1, two Term IH plus
domain/codomain Ty payloads.  Cast on the outer result; discharge via
weaken_appPi_unfolds + castInvariant. -/
theorem isTotalOnWeaken_appPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIH : IsTotalOnWeaken functionTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.appPi functionTerm argumentTerm) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken)))).isSome by
    rw [weaken_appPi_unfolds newType functionTerm argumentTerm]
    show ((Ty.subst0_rename_commute codomainType domainType argumentRaw
        RawRenaming.weaken).symm ▸
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken)))).strengthenTyped?.isSome
          = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next functionRecurse =>
          exfalso
          have totHyp := functionIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType functionTerm))) = true :=
            functionRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            dsimp only [strengthenTyped?] at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- `Term.weaken` arm reshape for `Term.pair`.

The rename arm has INNER cast on `secondValue`: the head is `Term.pair`
(no outer cast), but the secondValue argument is wrapped in
`Ty.subst0_rename_commute ... ▸ ...`.  Proved by `rfl`.

Note: `Ty.weaken` is defined as `Ty.rename RawRenaming.weaken`, but
they may not be defeq in all positions; this lemma uses the
`.rename RawRenaming.weaken` form explicitly. -/
theorem weaken_pair_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (newType : Ty level scope)
    (firstValue : Term context firstType firstRaw)
    (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Term.weaken newType (Term.pair firstValue secondValue) =
      Term.pair (Term.weaken newType firstValue)
        ((Ty.subst0_rename_commute secondType firstType firstRaw
          RawRenaming.weaken) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) secondValue :
            Term (context.cons newType)
              ((secondType.subst0 firstType firstRaw).rename RawRenaming.weaken)
              (secondRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 2-IH non-binder totality through INNER Eq.mpr cast: `Term.pair`.

The cast is on the `secondValue` subterm, so the dispatcher's match on
`Term.pair` head succeeds, but the recursion on the cast term doesn't
directly hit the secondIH.  Use cast invariance to bridge the inner
cast back to the un-cast form. -/
theorem isTotalOnWeaken_pair {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIH : IsTotalOnWeaken firstValue)
    (secondIH : IsTotalOnWeaken secondValue) :
    IsTotalOnWeaken (Term.pair firstValue secondValue) := by
  intro newType
  -- Term.weaken nt (Term.pair fv sv) =
  --   Term.pair (Term.weaken nt fv) (eq ▸ Term.weaken nt sv)
  -- Rewrite via weaken_pair_unfolds to expose the inner cast explicitly,
  -- then the dispatcher's match on Term.pair head fires.
  rw [weaken_pair_unfolds newType firstValue secondValue]
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next secondTypeFails =>
      exfalso
      have secondTypeSuccess :
          (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some secondType := by
        have := Ty.partialStrengthen?_rename_some secondType
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [Ty.rename_identity] at this
        exact this
      rw [secondTypeSuccess] at secondTypeFails
      cases secondTypeFails
  · split
    · next firstRecurse =>
        exfalso
        have totHyp := firstIH newType
        dsimp only [strengthenTyped?] at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType firstValue))) = true :=
          firstRecurse ▸ totHyp
        cases this
    · split
      · next secondRecurse =>
          exfalso
          -- secondRecurse : (eq ▸ Term.rename _ secondValue).partialStrengthenTyped? = none
          -- (Term.weaken newType secondValue = Term.rename (weakenStep) secondValue,
          --  definitional equality through @[reducible] Term.weaken.)
          --
          -- secondIH gives (Term.weaken nt sv).strengthenTyped?.isSome = true,
          -- castInvariant says (eq ▸ ...).strengthenTyped?.isSome = (...).strengthenTyped?.isSome,
          -- so secondRecurse's none contradicts.
          have totHyp := secondIH newType
          dsimp only [strengthenTyped?] at totHyp
          have invariance :=
            strengthenTyped?_isSome_castInvariant
              (Term.rename (TermRenaming.weakenStep context newType) secondValue)
              (Ty.subst0_rename_commute secondType firstType firstRaw
                RawRenaming.weaken)
          dsimp only [strengthenTyped?] at invariance
          -- invariance: (eq ▸ Term.rename ... sv).partialStrengthenTyped? _ .isSome
          --           = (Term.rename ... sv).partialStrengthenTyped? _ .isSome
          rw [secondRecurse] at invariance
          -- invariance: false = (Term.rename ... sv).partialStrengthenTyped? _ .isSome
          -- which is `Option.isSome none = ...`, i.e. `false = ...`
          -- After rw, invariance becomes `none.isSome = ...isSome`
          -- And totHyp says `... .isSome = true`
          rw [totHyp] at invariance
          cases invariance
      · rfl

end Term

end LeanFX2

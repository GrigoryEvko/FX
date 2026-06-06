import FX1Poly.Typed.HasType
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeSubstitution — typed substitution (the β-engine)

The keystone typed metatheory lemma (P6): `HasType` is preserved
under substitution.  This is what `app`'s β-reduction `B.subst0 a` needs to
preserve typing, so it is the engine of typed subject reduction's β case.
Sibling to typed weakening: weakening is the RENAMING action on a derivation,
substitution is the full SUBSTITUTION action.  Both are "whiskering" by a context morphism in the fibration
reading — renaming whiskers by a `Fin → Fin`, substitution by a
`Fin → RawTerm`.

## Structure: general lemma + subst0 corollary

`substRespectingContext` is the general statement over a VARIABLE source
context with a substitution-typing side condition (each source variable's
substituent is target-typed at the substituted looked-up type).  It inducts
cleanly — exactly the shape of `renameRespectingContext`, with `Conv.subst`
(#370) in the `conv` case instead of `Conv.rename`.

`substituteUnderBinding` is the single-substitution corollary the β-rule
cites: substituting a well-typed `argument` for de Bruijn 0.  It instantiates
the general lemma with `RawTermSubst.singleton argument` and discharges the
side condition by a `Fin` 0/successor split.

The per-cell `subst` computations + the binder-crossing commutations these
arms consume live in the `CellSubstitution` substrate (extracted so they stand
on the cell constructors alone); this file is the `HasType`-specific
substitution engine over them.

Critically `Conv.trans`-free, like weakening: the substitution machinery
rides existing `Conv.subst`, never composing conversions.  So the β-engine
does not depend on raw confluence.

## Zero-axiom verification

The induction + `rw` + the `Fin`-split discharge stay `propext`-free (the
underlying cell computations reduce by `rfl` in `CellSubstitution`).
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-! ## The general substitution lemma

`HasType` is preserved along any substitution whose substituents are
target-typed at the substituted source-binding types.  The
`targetContext` / substitution / side-condition are quantified inside the
conclusion so `induction typed` carries them in the motive (the source
context is an index of `typed`, fixed across the derivation).  The
binder-introducing arms (`piFormation` / `sigmaFormation`) lift the side
condition across the fresh binder; the leaf arms pass it verbatim. -/
theorem HasType.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (typed : HasType profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasType profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasType profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  induction typed with
  | var sourceContext index =>
      intro targetScope targetContext substitution substitutionTyped
      rw [subst_variableCell]
      exact substitutionTyped index
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise ihReclassifier =>
      intro targetScope targetContext substitution substitutionTyped
      have premiseTyped :=
        ihTypedPremise targetContext substitution substitutionTyped
      have reclassifierTypedSubst :=
        ihReclassifier targetContext substitution substitutionTyped
      rw [subst_universeCodeCell] at reclassifierTypedSubst
      exact HasType.conv levelExpr flag premiseTyped
        (Conv.subst substitution converts) reclassifierTypedSubst
  | universeFormation sourceContext levelExpr flag =>
      intro targetScope targetContext substitution substitutionTyped
      rw [subst_universeCodeCell, subst_universeCodeCell]
      exact HasType.universeFormation targetContext levelExpr flag
  | piFormation sourceContext domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      intro targetScope targetContext substitution substitutionTyped
      rw [subst_piTyCodeCell, subst_universeCodeCell]
      refine HasType.piFormation targetContext _ _ domainLevel codomainLevel flag ?_ ?_
      · -- domain code is substituted by the substitution itself
        have domainSubst :=
          ihDomain targetContext substitution substitutionTyped
        rw [subst_universeCodeCell] at domainSubst
        exact domainSubst
      · -- codomain lives under one fresh binder: its IH fires with the LIFTED
        -- substitution into the extended target context; the lifted
        -- substitution-typing condition splits 0/successor — position 0 is the
        -- fresh variable (`var`), position k+1 is a weakened substituent
        -- (`weakenUnderBinding`), both crossing the binder via
        -- `subst_lift_weaken_commute`
        have codomainSubst :=
          ihCodomain (targetContext.cons (RawTerm.subst substitution domainCode))
            (RawTermSubst.lift substitution) ?liftedCondition
        · rw [subst_universeCodeCell] at codomainSubst
          exact codomainSubst
        case liftedCondition =>
          intro index
          obtain ⟨indexValue, indexBound⟩ := index
          cases indexValue with
          | zero =>
              rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
              exact HasType.var
                (targetContext.cons (RawTerm.subst substitution domainCode))
                ⟨0, Nat.succ_pos targetScope⟩
          | succ k =>
              rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
              exact (substitutionTyped ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
                (RawTerm.subst substitution domainCode)
  | sigmaFormation sourceContext domainCode codomainCode domainLevel codomainLevel
      flag domainTyped codomainTyped ihDomain ihCodomain =>
      -- exact mirror of the `piFormation` case: `subst_sigmaTyCodeCell`
      -- distributes the substitution, the domain IH fires bare, and the codomain
      -- IH fires under the LIFTED substitution with the same 0/successor split
      -- (fresh `var` at 0, weakened substituent at k+1, both via
      -- `subst_lift_weaken_commute`)
      intro targetScope targetContext substitution substitutionTyped
      rw [subst_sigmaTyCodeCell, subst_universeCodeCell]
      refine HasType.sigmaFormation targetContext _ _ domainLevel codomainLevel flag ?_ ?_
      · have domainSubst :=
          ihDomain targetContext substitution substitutionTyped
        rw [subst_universeCodeCell] at domainSubst
        exact domainSubst
      · have codomainSubst :=
          ihCodomain (targetContext.cons (RawTerm.subst substitution domainCode))
            (RawTermSubst.lift substitution) ?liftedCondition
        · rw [subst_universeCodeCell] at codomainSubst
          exact codomainSubst
        case liftedCondition =>
          intro index
          obtain ⟨indexValue, indexBound⟩ := index
          cases indexValue with
          | zero =>
              rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
              exact HasType.var
                (targetContext.cons (RawTerm.subst substitution domainCode))
                ⟨0, Nat.succ_pos targetScope⟩
          | succ k =>
              rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
              exact (substitutionTyped ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
                (RawTerm.subst substitution domainCode)

/-- Typed single-substitution (the β-engine): substituting a well-typed
`argument` for de Bruijn 0 preserves typing.  The corollary of
`substRespectingContext` that `app`'s β-reduction `B.subst0 a` cites — given
`Γ, A ⊢ subject : classifier` and `Γ ⊢ argument : A`, the substituted subject
`subject[argument]` has the substituted type `classifier[argument]` in `Γ`.

The side condition is discharged by a `Fin` 0/successor split: position 0
returns the argument (typed by `argumentTyped`), position k+1 returns a
shifted variable (typed by `var`) — and the looked-up binding types cancel
their weakening against the singleton substitution. -/
theorem HasType.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)} (argument : RawTerm scope)
    (typed : HasType profile (context.cons argType) subject classifier)
    (argumentTyped : HasType profile context argument argType) :
    HasType profile context
      (RawTerm.subst0 subject argument)
      (RawTerm.subst0 classifier argument) := by
  refine typed.substRespectingContext context
    (RawTermSubst.singleton argument) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasType profile context argument
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken argType))
      rw [subst_singleton_renameWeaken_cancel]
      exact argumentTyped
  | succ k =>
      show HasType profile context
          (variableCell ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken
            (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [subst_singleton_renameWeaken_cancel]
      exact HasType.var context ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩

end FX1Poly.Typed

import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescPiSubstitution

/-! # FX1Poly/Typed/ReducibleSemanticRules
    — the fundamental theorem's semantic typing rules under a closing substitution (#425)

The Girard-Tait fundamental theorem over `HasTypeDescPi` is a thin induction on the derivation whose
arms dispatch to SEMANTIC TYPING RULES "under a closing substitution `γ`": each rule takes the induction
hypotheses (the premises' reducibility, already closed by `γ`) and produces the conclusion's reducibility
(also closed by `γ`).  This file accumulates those rules — one per `HasTypeDescPi` constructor — lifting
the shipped raw membership rules (`IsReducibleMemberAt.application` / `.castAlongConv` / `.abstraction`,
and `ReducibleEnvAt.lookupReducible`) through the substitution-commutation lemmas that re-express
`subst γ (cell …)` as `cell (subst γ …)`.

## The application (`piElim`) arm — shipped here

`HasTypeDescPi.piElim` types `appCell functionTerm argument : subst0 codomainCode argument` from
`functionTerm : Π domainCode. codomainCode` and `argument : domainCode`.  Its semantic counterpart takes
the γ-closed reducibility of the function and argument and produces the γ-closed reducibility of the
application at the γ-closed dependent output.  The technical crux is the β-substitution commutation
`RawTerm.subst0_subst_commute`: `subst γ (subst0 codomainCode argument)` is exactly
`subst0 (subst (lift γ) codomainCode) (subst γ argument)` — the dependent output of the substituted
function/argument — so the raw `IsReducibleMemberAt.application` (over the substituted domain/codomain
candidates) lands precisely at the γ-closed classifier.  `subst_appCell` / `subst_piTyCodeCell` (both
`rfl`) re-express the application and Π cells; `iterateLiftRaw γ 1 ≡ RawTermSubst.lift γ` by `rfl`.

This is the literal body of the fundamental theorem's `piElim` arm, threaded at a FIXED `level` — the
elimination rule introduces no universe nesting, so the level rides straight through (the level decrease
is confined to the universe/formation arms).

## Zero-axiom verification

Two `rfl` rewrites (`subst_appCell`, `subst_piTyCodeCell`) + the β-commutation `RawTerm.subst0_subst_commute`
+ the shipped `IsReducibleMemberAt.application` (defeq-unified through `iterateLiftRaw γ 1 ≡ lift γ`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **Semantic Π elimination under a closing substitution (the `piElim` arm of the fundamental theorem).**
Given that a closing substitution `substitution` sends `functionTerm` to a reducible member of the closed
Π-type `subst (piTyCodeCell domainCode codomainCode)` and `argument` to a reducible member of the closed
domain, it sends `appCell functionTerm argument` to a reducible member of the closed dependent output
`subst (subst0 codomainCode argument)`.

The β-substitution commutation `RawTerm.subst0_subst_commute` re-expresses that closed output as
`subst0 (subst (lift substitution) codomainCode) (subst substitution argument)` — the dependent output of
the substituted pieces — so the shipped raw `IsReducibleMemberAt.application` applies directly (`subst_appCell`
/ `subst_piTyCodeCell` re-express the cells, both `rfl`; `iterateLiftRaw substitution 1 ≡ lift substitution`
by `rfl`).  The `level` is threaded unchanged — elimination introduces no universe nesting. -/
theorem IsReducibleMemberAt.applicationUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argument : RawTerm scope}
    (substitution : RawTermSubst scope targetScope)
    (functionReducible : IsReducibleMemberAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      (RawTerm.subst substitution functionTerm))
    (argumentReducible : IsReducibleMemberAt level
      (RawTerm.subst substitution domainCode)
      (RawTerm.subst substitution argument)) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution (RawTerm.subst0 codomainCode argument))
      (RawTerm.subst substitution (appCell functionTerm argument)) := by
  rw [subst_piTyCodeCell] at functionReducible
  rw [subst_appCell, RawTerm.subst0_subst_commute]
  exact IsReducibleMemberAt.application functionReducible argumentReducible

/-- **Semantic conversion under a closing substitution (the `conv` arm of the fundamental theorem).**
Given that a closing `substitution` sends `subject` to a reducible member of the closed `classifier`, and
that the closed `reclassifier` is itself a reducible type at `level` — which the fundamental theorem obtains
by `tarskiDecode`-ing the `reclassifier : Type@e` premise's induction hypothesis taken at `level + 1` — it
sends `subject` to a reducible member of the closed `reclassifier`.  The membership transports across the
SUBSTITUTED conversion `Conv.subst substitution converts` via the shipped `IsReducibleMemberAt.castAlongConv`.
The `level` is threaded unchanged — conversion introduces no universe nesting. -/
theorem IsReducibleMemberAt.castAlongConvUnderSubst {scope targetScope : Nat} {level : Nat}
    {classifier reclassifier subject : RawTerm scope}
    {candidateRight : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (subjectReducible : IsReducibleMemberAt level
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject))
    (reclassifierReducible : ReducibleTypeAt level
      (RawTerm.subst substitution reclassifier) candidateRight)
    (converts : Conv classifier reclassifier) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution reclassifier) (RawTerm.subst substitution subject) :=
  IsReducibleMemberAt.castAlongConv subjectReducible reclassifierReducible
    (Conv.subst substitution converts)

end FX1Poly.Typed

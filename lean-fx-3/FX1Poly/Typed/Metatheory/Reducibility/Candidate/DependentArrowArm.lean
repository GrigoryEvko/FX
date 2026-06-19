import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateShapeValidity
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeAbstraction

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/DependentArrowArm
    — the function-space (dependentProduct) intro + elim FT arms (FTGEN-8 / FTGEN-10)

The `dependentProduct` descriptor shape (Π / arrow) is the one premise-NEEDING data-free candidate: its
candidate `DependentArrowCandidate dom cod := fun f => ∀ a, dom a → cod a (app f a)` references the sub-
candidates.  This file exposes its two FT arms at the arc, keyed to the shape, by reusing the shipped Core
lemmas:

  * **FTGEN-10 (general-elim / `app`)** — `dependentProductElim`: applying a member of the Π candidate to a
    reducible argument lands in that argument's codomain candidate.  This IS the candidate's defining
    property (`DependentArrowCandidate.application` = `f a ha`) — the elim arm is definitional.
  * **FTGEN-8 (graded-intro / `λ`)** — `dependentProductIntro`: `λ body` is in the Π candidate when, for every
    reducible argument, the body's substitution instance is in that argument's codomain candidate — the
    classical Tait abstraction lemma (`DependentArrowCandidate.abstraction`).  The β-redex
    `app (λ body) a ↝ subst0 body a` head-expands, so the codomain candidate's `HeadExpansionClosed` carries
    membership back; the argument's SN (from the domain candidate's CR1) and the domain annotation's SN feed
    the closure.  This is the genuinely hard direction.

Together with `dependentProductCandidate` (the shape's candidate, an alias of `DependentArrowCandidate`) this
is the full function-space former at the descriptor level: candidate + intro + elim.  Its CR validity is the
conditional `isDependentArrowReducible_isReducibilityCandidate` (Core), exposed by the formation arm.

## Zero-axiom verification

`dependentProductElim` / `dependentProductIntro` are direct applications of the shipped, audited Core lemmas
`DependentArrowCandidate.application` / `.abstraction`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The `dependentProduct` (Π / arrow) shape's candidate: the dependent function space over a domain
candidate and a codomain candidate family — the kernel `DependentArrowCandidate`. -/
@[reducible] def dependentProductCandidate {scope : Nat}
    (domainCandidate : RawTerm scope → Prop)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)) : RawTerm scope → Prop :=
  DependentArrowCandidate domainCandidate codomainCandidate

/-- **★ FTGEN-10 — the general-elim (`app`) arm.**  Applying a Π-candidate member to a reducible argument
lands in that argument's codomain candidate.  The defining property of the function-space candidate (the elim
arm is definitional). -/
theorem dependentProductElim {scope : Nat}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {functionTerm argument : RawTerm scope}
    (functionReducible : dependentProductCandidate domainCandidate codomainCandidate functionTerm)
    (argumentReducible : domainCandidate argument) :
    codomainCandidate argument
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) :=
  DependentArrowCandidate.application functionReducible argumentReducible

/-- **★ FTGEN-8 — the graded-intro (`λ`) arm.**  `λ body` is a Π-candidate member when every reducible
argument's body-substitution lands in its codomain candidate.  The Tait abstraction lemma: the β-redex head-
expands and the codomain candidate's `HeadExpansionClosed` carries membership back, fed by the domain
annotation's and argument's strong normalization. -/
theorem dependentProductIntro {scope : Nat}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainAnnSN : IsStronglyNormalizing domainAnn)
    (domainArgumentsSN :
      ∀ argument : RawTerm scope, domainCandidate argument → IsStronglyNormalizing argument)
    (codomainClosed :
      ∀ argument : RawTerm scope, domainCandidate argument →
        HeadExpansionClosed (codomainCandidate argument))
    (bodyReducible :
      ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument (RawTerm.subst0 body argument)) :
    dependentProductCandidate domainCandidate codomainCandidate
      (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) :=
  DependentArrowCandidate.abstraction domainAnnSN domainArgumentsSN codomainClosed bodyReducible

end FX1Poly.Typed

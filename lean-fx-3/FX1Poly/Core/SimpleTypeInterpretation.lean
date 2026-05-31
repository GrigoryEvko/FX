import FX1Poly.Core.HeadExpansionClosure
import FX1Poly.Core.RawTermSubst0Commute

/-! # Foundation/PolyCell/Core/SimpleTypeInterpretation
    — the simple-type reducibility interpretation `Red : SimpleType → candidate`

Strong normalization of the grown Π-fragment factors through the **simple-type skeleton**:
β-reduction ignores type dependency, so SN of a well-typed term follows from reducibility at the
*erased* simple type.  This file defines that skeleton and the Tait reducibility interpretation

  `Red base            = IsStronglyNormalizing`   (base/atomic types ↦ the SN candidate)
  `Red (arrow dom cod) = IsArrowReducible (Red dom) (Red cod)`   (Π ↦ the function-space candidate)

and proves the first of the two properties the fundamental theorem combines:

* `Red_headExpansionClosed` — every interpreted type is head-expansion-closed, by induction on the
  simple type (SN base case + the arrow former's preservation).

The companion property — every `Red T` is a reducibility candidate (which feeds the variable case
and the `Red ⟹ SN` corollary) — is the next brick; it needs a `Red`-reducible witness at every type
(the closed constant-function construction) and the `subst0 (weaken t) a = t` cancellation lemma.

## Zero-axiom verification

A plain inductive + a structural recursive `def` + a two-case induction discharging to the shipped
closure theorems.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- Simple types — the erasure skeleton of the grown Π-fragment: a base sort and arrows. -/
inductive SimpleType : Type where
  | base : SimpleType
  | arrow : SimpleType → SimpleType → SimpleType

/-- The Tait reducibility interpretation: base ↦ the SN candidate, arrow ↦ the function-space
candidate `IsArrowReducible`.  Structural recursion on the simple type. -/
def Red {scope : Nat} : SimpleType → RawTerm scope → Prop
  | .base => IsStronglyNormalizing
  | .arrow domain codomain => IsArrowReducible (Red domain) (Red codomain)

/-- Every interpreted type is head-expansion-closed.  Induction on the simple type: the base case is
the SN candidate's closure (`isStronglyNormalizing_headExpansionClosed`), the arrow case is the
former's preservation (`isArrowReducible_headExpansionClosed`).  One of the two ingredients the
fundamental theorem's λ case combines. -/
theorem Red_headExpansionClosed {scope : Nat} (simpleType : SimpleType) :
    HeadExpansionClosed (Red (scope := scope) simpleType) := by
  induction simpleType with
  | base => exact isStronglyNormalizing_headExpansionClosed
  | arrow domain codomain _domainClosed codomainClosed =>
      show HeadExpansionClosed (IsArrowReducible (Red domain) (Red codomain))
      exact isArrowReducible_headExpansionClosed codomainClosed

/-- A closed `Red`-reducible witness at every simple type — the inhabitant the arrow candidate's CR1
needs.  Base: the `optionNone` atom (a closed normal form, hence SN).  Arrow: the constant function
`λ. weaken (closedWitness codomain)`, which on any argument β-reduces — via the weakening
cancellation `weaken_subst_singleton` — to the codomain's own witness. -/
def closedWitness {scope : Nat} : SimpleType → RawTerm scope
  | .base => .mkGen .gen_optionNone () .childNil
  | .arrow _domain codomain =>
      .mkGen .gen_lam () (.childCons (RawTerm.weaken (closedWitness codomain)) .childNil)

/-- Every interpreted type is BOTH a reducibility candidate AND inhabited by its closed witness.
The two halves are proved by a SINGLE induction because they support each other at strictly smaller
types — the arrow candidate's CR1 consumes the DOMAIN witness, while the arrow witness's reducibility
consumes the DOMAIN's CR1 (for `SN argument`) and the CODOMAIN's head-expansion closure.  This closed
witness construction is why no scope restriction (`scope > 0`) or weakening machinery is needed: a
reducible argument exists at every scope, including the empty context. -/
theorem Red_candidate_and_witness {scope : Nat} (simpleType : SimpleType) :
    IsReducibilityCandidate (Red (scope := scope) simpleType) ∧
      Red (scope := scope) simpleType (closedWitness (scope := scope) simpleType) := by
  induction simpleType with
  | base =>
      exact ⟨isStronglyNormalizing_isReducibilityCandidate, optionNone_isStronglyNormalizing⟩
  | arrow domain codomain domainInductiveHypothesis codomainInductiveHypothesis =>
      obtain ⟨domainCandidate, domainWitnessReducible⟩ := domainInductiveHypothesis
      obtain ⟨codomainCandidate, codomainWitnessReducible⟩ := codomainInductiveHypothesis
      refine ⟨?candidate, ?witness⟩
      · show IsReducibilityCandidate (IsArrowReducible (Red domain) (Red codomain))
        exact isArrowReducible_isReducibilityCandidate domainCandidate codomainCandidate
          (closedWitness domain) domainWitnessReducible
      · show IsArrowReducible (Red domain) (Red codomain)
            (.mkGen .gen_lam ()
              (.childCons (RawTerm.weaken (closedWitness codomain)) .childNil))
        intro argument argumentReducible
        have argumentSN : IsStronglyNormalizing argument :=
          domainCandidate.stronglyNormalizing argumentReducible
        have cancelEquation :
            RawTerm.subst0 (RawTerm.weaken (closedWitness codomain)) argument =
              closedWitness codomain :=
          RawTerm.weaken_subst_singleton (closedWitness codomain) argument
        refine Red_headExpansionClosed codomain
          (body := RawTerm.weaken (closedWitness codomain)) (argument := argument)
          (spine := []) argumentSN ?_
        show Red codomain (RawTerm.subst0 (RawTerm.weaken (closedWitness codomain)) argument)
        rw [cancelEquation]
        exact codomainWitnessReducible

/-- Every interpreted type is a reducibility candidate — the projection feeding the fundamental
theorem's variable case (`containsVariable`) and the eventual `Red ⟹ SN` corollary (CR1). -/
theorem Red_isReducibilityCandidate {scope : Nat} (simpleType : SimpleType) :
    IsReducibilityCandidate (Red (scope := scope) simpleType) :=
  (Red_candidate_and_witness simpleType).1

/-- **Reducible ⟹ strongly normalizing** (CR1 at every type) — the SN-extraction direction that,
composed with the fundamental theorem, yields strong normalization of well-typed terms. -/
theorem Red_isStronglyNormalizing {scope : Nat} {simpleType : SimpleType}
    {term : RawTerm scope} (reducible : Red simpleType term) :
    IsStronglyNormalizing term :=
  (Red_isReducibilityCandidate simpleType).stronglyNormalizing reducible

/-- **The variable case** of the fundamental theorem: a variable is reducible at every type, because
it is contained in every reducibility candidate (`containsVariable`). -/
theorem reducibleVariable {scope : Nat} (simpleType : SimpleType) (index : Fin scope) :
    Red simpleType (.mkGen .gen_var index .childNil) :=
  (Red_isReducibilityCandidate simpleType).containsVariable index

/-- **The application (Π-elimination) case** of the fundamental theorem: a reducible function applied
to a reducible argument is reducible in the codomain — by unfolding the function-space predicate. -/
theorem reducibleApplication {scope : Nat} {domainType codomainType : SimpleType}
    {function argument : RawTerm scope}
    (functionReducible : Red (.arrow domainType codomainType) function)
    (argumentReducible : Red domainType argument) :
    Red codomainType
      (.mkGen .gen_app () (.childCons function (.childCons argument .childNil))) :=
  functionReducible argument argumentReducible

/-- **The λ-abstraction (Π-introduction) case** of the fundamental theorem — its heart.  If the body
is reducible in the codomain for every reducible argument substituted in, then the λ is reducible at
the arrow type.  The β-redex `app (lam body) argument` inherits codomain membership from its
contractum `subst0 body argument` by head-expansion closure, with `SN argument` supplied by the
domain candidate's CR1.  No type-erasure or substitution machinery enters here — this is the purely
semantic content the eventual syntactic induction discharges. -/
theorem reducibleAbstraction {scope : Nat} {domainType codomainType : SimpleType}
    {body : RawTerm (scope + 1)}
    (bodyReducible : ∀ argument : RawTerm scope, Red domainType argument →
      Red codomainType (RawTerm.subst0 body argument)) :
    Red (.arrow domainType codomainType)
      (.mkGen .gen_lam () (.childCons body .childNil)) := by
  intro argument argumentReducible
  have argumentSN : IsStronglyNormalizing argument :=
    (Red_isReducibilityCandidate domainType).stronglyNormalizing argumentReducible
  exact Red_headExpansionClosed codomainType
    (body := body) (argument := argument) (spine := []) argumentSN
    (bodyReducible argument argumentReducible)

end FX1Poly.Core

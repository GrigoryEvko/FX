import FX1Poly.Core.ReducibleMember
import FX1Poly.Core.ReducibleTypeForwardStepStar

/-! # Foundation/PolyCell/Core/ReducibleTypeWellFormed
    — the semantic well-formed-type predicate (the type-level companion to `IsReducibleMember`)

`ReducibleType typeCode candidate` is a RELATION assigning a candidate to a code.  Often one needs only
that a code IS a reducible type — that it denotes SOME candidate — without naming it:

  `IsReducibleType typeCode := ∃ candidate, ReducibleType typeCode candidate`.

This is the TYPE-level analogue of `IsReducibleMember`: where `IsReducibleMember T t` says "t inhabits the
candidate of T", `IsReducibleType T` says "T has a candidate at all".  It is exactly what the fundamental
theorem's `conv` arm needs (`IsReducibleMember.castAlongConv` consumes a `ReducibleType` witness for the
reclassifier, recovered by destructuring `IsReducibleType (subst γ reclassifier)`), and the conclusion
shape of the TYPE-level soundness (well-formed type → reducible type) the conv arm and the eventual
candidate-valued universe build on.

This file ships the predicate and its four constructors/closure properties, each a thin wrapper over the
shipped `ReducibleType` machinery:

  * `IsReducibleType.forwardStepStar` — reducible types stay reducible along reduction (forward closure).
  * `IsReducibleType.ofNeutral` — a weak-head-normal non-Π code is a reducible type (the SN candidate);
    in particular every universe code and stuck/neutral former.
  * `IsReducibleType.piTyCode` — a Π-code with a reducible domain and a reducible (per-argument) codomain
    is a reducible type (the dependent-arrow candidate).
  * `IsReducibleMember.isReducibleType` — if a term inhabits a type's candidate, that type is reducible.

## Zero-axiom verification

Each is a `let`-destructure + anonymous constructor over the shipped `ReducibleType` arms / closures.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration
by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- **The semantic well-formed-type predicate.**  A code is a reducible type when it denotes some
reducibility candidate.  The type-level analogue of `IsReducibleMember`. -/
def IsReducibleType {scope : Nat} (typeCode : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleType typeCode candidate

/-- **Reducible types are forward-closed under reduction.**  A reducible type stays reducible (at the
same candidate) along any multi-step reduction — the type-level forward closure. -/
theorem IsReducibleType.forwardStepStar {scope : Nat} {firstType finalType : RawTerm scope}
    (reducibleType : IsReducibleType firstType) (reduction : StepStar firstType finalType) :
    IsReducibleType finalType :=
  let ⟨candidate, reducible⟩ := reducibleType
  ⟨candidate, reducible.forwardStepStar reduction⟩

/-- **A weak-head-normal non-Π code is a reducible type.**  It denotes the strong-normalization candidate
(`ReducibleType.neutral`); in particular every universe code, every stuck/neutral former, and every
variable-as-type is a reducible type. -/
theorem IsReducibleType.ofNeutral {scope : Nat} {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode) :
    IsReducibleType typeCode :=
  ⟨IsStronglyNormalizing, ReducibleType.neutral noWeakHeadStep notPiType⟩

/-- **A Π-code over reducible components is a reducible type.**  Given a reducible domain candidate and,
for every domain-reducible argument, a reducible candidate for the instantiated codomain, the Π-code
denotes the dependent-arrow candidate — the type-level Π-formation soundness. -/
theorem IsReducibleType.piTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    (domainReducible : ReducibleType domainCode domainCandidate)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) :
    IsReducibleType
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  ⟨_, ReducibleType.piType codomainCandidate domainReducible codomainReducible⟩

/-- **An inhabited type is a reducible type.**  If a term lies in a type's candidate, the type denotes
that candidate, hence is reducible — the bridge from `IsReducibleMember` down to `IsReducibleType`. -/
theorem IsReducibleMember.isReducibleType {scope : Nat} {typeCode term : RawTerm scope}
    (member : IsReducibleMember typeCode term) : IsReducibleType typeCode :=
  let ⟨candidate, reducible, _membership⟩ := member
  ⟨candidate, reducible⟩

/-- **A universe code is a reducible type** — the fundamental theorem's type-formation `universeFormation`
arm, at the `IsReducibleType` level.  A universe code `Type@e` is a weak-head-normal non-Π leaf (its only
candidate WeakHeadStep arm is `rootIota`, refuted since no `IotaHeadStep` fires on a `gen_universeCode`
root; its root is `gen_universeCode ≠ gen_piTyCode`), so `ofNeutral` denotes it the strong-normalization
candidate.  This specializes `ofNeutral` with the neutral side-conditions discharged once for universe
codes — exactly what the type-FT's universe-formation arm reads (`Type@e` is a reducible type, no per-use
re-derivation of weak-head-normality). -/
theorem IsReducibleType.universeCode {scope : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleType (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) :=
  IsReducibleType.ofNeutral
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)

/-- **Choice-free Π introduction (the fundamental theorem's `piIntro` arm).**  `lam body` is a reducible
member of the Π-type when, for every reducible argument, (i) the instantiated codomain is a reducible TYPE
and (ii) the body's substitution instance is a reducible member of it.  Unlike `IsReducibleMember.abstraction`,
the codomain candidate is NOT supplied as a uniform function — only the EXISTENTIAL `IsReducibleType` (what
the fundamental theorem's codomain type-formation hypothesis delivers per argument).  The canonical candidate
`ReducibleType.atMemberPredicate` resolves the uniformity WITHOUT choice: the fixed codomain candidate family
is `fun argument => IsReducibleMember (subst0 codomainCode argument)`, a genuine function of the type, and at
each argument `atMemberPredicate` turns the existential reducible-type witness into reducibility AT that
canonical candidate, while the body hypothesis IS membership in it definitionally.  This is the keystone the
`ofPointwiseIff` arm was added to enable. -/
theorem IsReducibleMember.abstractionAtMemberPredicate {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleType domainCode domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainIsReducibleType : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleType (RawTerm.subst0 codomainCode argument))
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleMember (RawTerm.subst0 codomainCode argument) (RawTerm.subst0 body argument)) :
    IsReducibleMember
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons body .childNil)) :=
  IsReducibleMember.abstraction
    (codomainCandidate := fun argument => IsReducibleMember (RawTerm.subst0 codomainCode argument))
    domainReducible domainArgumentsSN
    (fun argument argumentInDomain =>
      (codomainIsReducibleType argument argumentInDomain).elim
        (fun _witnessCandidate witnessReducible => ReducibleType.atMemberPredicate witnessReducible))
    bodyReducible

end FX1Poly.Core

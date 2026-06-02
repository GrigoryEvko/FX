import FX1Poly.Core.ReducibleMember
import FX1Poly.Core.StrongNormalizationConstructors

/-! # Foundation/PolyCell/Core/ReducibleMemberNeutral
    — membership at a neutral classifier is exactly strong normalization

The `neutral` arm of `ReducibleType` assigns the strong-normalization candidate to EVERY weak-head-normal
non-Π type (a variable, a stuck application/eliminator, a universe code, any non-Π former).  So semantic
membership at such a classifier collapses to a single, sharp statement:

  `IsReducibleMember classifier term ↔ IsStronglyNormalizing term`   (classifier neutral).

This is the semantic heart of why the reducibility model proves SN — every type whose code is a normal
leaf (in particular every universe code, the classifier of every well-formed TYPE) classifies EXACTLY
the strongly-normalizing terms.  The fundamental theorem's formation/universe arms read the `←` direction
(an SN formation subject is a member of its universe-code classifier); the `→` direction extracts SN from
membership (the candidate→SN bridge at a fixed neutral type, without the scope+1 of the general CR1).

## Zero-axiom verification

`ReducibleType.deterministic` against the `neutral` witness for the `→` direction; the explicit
`neutral`-candidate triple for the `←` direction.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Membership at a neutral classifier is exactly strong normalization.**  A weak-head-normal non-Π
type denotes the strong-normalization candidate (`ReducibleType.neutral`), so a term is a reducible
member of it precisely when strongly normalizing.  `→`: the member's candidate coincides with the SN
candidate by `ReducibleType.deterministic`.  `←`: the SN candidate is itself a witnessing candidate. -/
theorem IsReducibleMember.atNeutralClassifier {scope : Nat} {classifier term : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
    (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode) :
    IsReducibleMember classifier term ↔ IsStronglyNormalizing term := by
  constructor
  · intro member
    obtain ⟨candidate, reducible, membership⟩ := member
    exact (ReducibleType.deterministic reducible
      (ReducibleType.neutral noWeakHeadStep notPiType) term).mp membership
  · intro stronglyNormalizing
    exact ⟨IsStronglyNormalizing, ReducibleType.neutral noWeakHeadStep notPiType, stronglyNormalizing⟩

/-- **The Π former inhabits its universe — the `genFormationPi` arm over the CONV-COMPLETE membership
layer.**  A Π-type code is a reducible member of any neutral non-Π universe classifier (every universe code
`Type@e` qualifies — a normal leaf, root `gen_universeCode`) exactly when it is strongly normalizing, which
`piTyCode_isStronglyNormalizing_of_domain_codomain` supplies from the children's strong normalization (their
fundamental-theorem induction hypotheses).  The `IsReducibleMember`/`ReducibleType` counterpart of the
choice-free `InterpretsType.fundamentalPiFormation` — this is the toolkit the fundamental theorem assembles
over, because it ALSO carries the `conv` arm (`IsReducibleMember.castAlongConv`), which the
`InterpretsType` interpretation cannot (its `baseType` arm admits redexes, so it is not forward-closed). -/
theorem IsReducibleMember.piFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainNormalizing : IsStronglyNormalizing domain)
    (codomainNormalizing : IsStronglyNormalizing codomain) :
    IsReducibleMember universeCode
      (.mkGen .gen_piTyCode () (.childCons domain (.childCons codomain .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (piTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing)

/-- **The Σ former inhabits its universe — the Σ twin of `piFormerInNeutralUniverse`.**  A Σ-type code is a
reducible member of any neutral non-Π universe classifier when strongly normalizing, supplied from the
children's strong normalization by `sigmaTyCode_isStronglyNormalizing_of_domain_codomain`.  Together with
`piFormerInNeutralUniverse` this discharges both `typingRuleDescOf` formers' universe membership over the
conv-complete `IsReducibleMember` layer. -/
theorem IsReducibleMember.sigmaFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainNormalizing : IsStronglyNormalizing domain)
    (codomainNormalizing : IsStronglyNormalizing codomain) :
    IsReducibleMember universeCode
      (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing)

/-- **The arrow former inhabits its universe — the non-dependent twin of `piFormerInNeutralUniverse`.**
An arrow-type code is a reducible member of any neutral non-Π universe classifier exactly when strongly
normalizing, supplied from the two endpoint codes' strong normalization by
`arrowCode_isStronglyNormalizing_of_domain_codomain`.  Both endpoint codes live at the SAME scope (the
arrow former binds no variable), unlike the Π/Σ formers whose codomain sits under one binder. -/
theorem IsReducibleMember.arrowFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {domain codomain : RawTerm scope}
    (domainNormalizing : IsStronglyNormalizing domain)
    (codomainNormalizing : IsStronglyNormalizing codomain) :
    IsReducibleMember universeCode
      (.mkGen .gen_arrowCode () (.childCons domain (.childCons codomain .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (arrowCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing)

/-- **The product former inhabits its universe.**  A product-type code is a reducible member of any
neutral non-Π universe classifier when both component codes are strongly normalizing, via
`productCode_isStronglyNormalizing_of_left_right`. -/
theorem IsReducibleMember.productFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {leftType rightType : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftType)
    (rightNormalizing : IsStronglyNormalizing rightType) :
    IsReducibleMember universeCode
      (.mkGen .gen_productCode () (.childCons leftType (.childCons rightType .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (productCode_isStronglyNormalizing_of_left_right leftNormalizing rightNormalizing)

/-- **The sum former inhabits its universe.**  A sum-type code is a reducible member of any neutral
non-Π universe classifier when both summand codes are strongly normalizing, via
`sumCode_isStronglyNormalizing_of_left_right`. -/
theorem IsReducibleMember.sumFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {leftType rightType : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftType)
    (rightNormalizing : IsStronglyNormalizing rightType) :
    IsReducibleMember universeCode
      (.mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (sumCode_isStronglyNormalizing_of_left_right leftNormalizing rightNormalizing)

/-- **The either former inhabits its universe.**  An either-type code is a reducible member of any
neutral non-Π universe classifier when both side codes are strongly normalizing, via
`eitherCode_isStronglyNormalizing_of_left_right`. -/
theorem IsReducibleMember.eitherFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {leftType rightType : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftType)
    (rightNormalizing : IsStronglyNormalizing rightType) :
    IsReducibleMember universeCode
      (.mkGen .gen_eitherCode () (.childCons leftType (.childCons rightType .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (eitherCode_isStronglyNormalizing_of_left_right leftNormalizing rightNormalizing)

/-- **The equivalence former inhabits its universe.**  An equivalence-type code is a reducible member of
any neutral non-Π universe classifier when both carrier codes are strongly normalizing, via
`equivCode_isStronglyNormalizing_of_source_target`.  Completes the non-dependent type-code former family
(arrow / product / sum / either / equiv) at the conv-complete neutral-universe membership layer, the twin
of the dependent `piFormerInNeutralUniverse` / `sigmaFormerInNeutralUniverse`. -/
theorem IsReducibleMember.equivFormerInNeutralUniverse {scope : Nat}
    {universeCode : RawTerm scope}
    (universeNoWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep universeCode reduct)
    (universeNotPiType : universeCode.rootGenerator ≠ Generator.gen_piTyCode)
    {sourceType targetType : RawTerm scope}
    (sourceNormalizing : IsStronglyNormalizing sourceType)
    (targetNormalizing : IsStronglyNormalizing targetType) :
    IsReducibleMember universeCode
      (.mkGen .gen_equivCode () (.childCons sourceType (.childCons targetType .childNil))) :=
  (IsReducibleMember.atNeutralClassifier universeNoWeakHeadStep universeNotPiType).mpr
    (equivCode_isStronglyNormalizing_of_source_target sourceNormalizing targetNormalizing)

end FX1Poly.Core

import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/HasTypeDescSubjectStronglyNormalizingNative
    — native (HasType-free) subject strong normalization for the description formation engine (HT-A3)

`HasTypeDescStronglyNormalizing.lean` proves `HasTypeDesc.isStronglyNormalizing` (every formation-typed SUBJECT
is strongly normalizing) by routing through the soundness map `HasTypeDesc.toHasType` into the native
pi/sigma-formation `HasType` core, whose subjects are SN.  That is a `HasType` coupling.

This file ships the HasType-FREE twin `HasTypeDesc.subjectStronglyNormalizingNative`, proved directly on the
formation engine's own structure — the migration target the public `isStronglyNormalizing` delegates to (part of
the phased `HasType` removal, parallel to `HasTypeDesc.uniquenessNative`).

## Structure

A formation subject is a variable, a universe code, a conversion of a subject, or a formed cell `mkGen
generator payload children` whose children are the formation telescope's types.  Variables and universe codes
are normal leaves; the `conv` arm preserves the subject; a formed cell steps only by stepping a child, so it is
SN once every child is SN.

* `RawTermChildren.allStronglyNormalizing` — the structural "every child is SN" predicate over a child spine.
* `formerCellStronglyNormalizingOfChildren` — the NON-recursive assembly: a formation former cell with all
  children SN is SN.  The formation table currently maps exactly `gen_piTyCode` / `gen_sigmaTyCode` (both
  two-child formers), discharged by the shipped `piTyCode` / `sigmaTyCode` two-child congruence SN closures; a
  non-former generator contradicts `isFormation` (`typingRuleDescOf … = none`).
* `HasTypeDesc.subjectStronglyNormalizingNative` ⋈ `DescTelescope.childrenStronglyNormalizingNative` — the
  genuine MUTUAL recursion (the `toHasType` shape): the subject recursion bottoms out the `genFormation` arm in
  the telescope recursion, which proves each head child SN by calling the subject recursion (a structural
  sub-derivation).  Equation-`match` form so the mutual recursion is recognised structural.

## Zero-axiom verification

Term-mode mutual recursion + the propext-free leaf-SN endpoints (`isStronglyNormalizing_of_noStep` +
`noStep_var` / `noStep_universeCode`) + the two-child congruence SN closures + full-enumeration `cases` over the
concrete-index `RawTermChildren` spines (clean — no partial match, no `propext`) + `simp only` on the structural
predicate.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe StepStar

/-- **Every child of a child spine is strongly normalizing.**  The structural per-child SN predicate the
formation telescope's SN recursion accumulates, consumed by `formerCellStronglyNormalizingOfChildren`. -/
def RawTermChildren.allStronglyNormalizing {binderShifts : List Nat} {baseScope : Nat} :
    RawTermChildren binderShifts baseScope → Prop
  | .childNil => True
  | .childCons head rest => IsStronglyNormalizing head ∧ rest.allStronglyNormalizing

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **A formation former cell with all children strongly normalizing is strongly normalizing.**  Non-recursive
assembly: the formation table maps exactly the two-child dependent type-formers (`gen_piTyCode` /
`gen_sigmaTyCode`) to a formation rule, so each is discharged by the shipped two-child congruence SN closure
(`piTyCode` / `sigmaTyCode`) over the destructured child spine; any other generator contradicts `isFormation`
(its `typingRuleDescOf` is `none`). -/
theorem formerCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : TypingRuleDesc}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) := by
  by_cases isPi : generator = Generator.gen_piTyCode
  · subst isPi
    cases payload
    cases children with
    | childCons _domain rest =>
        cases rest with
        | childCons _codomain rest2 =>
            cases rest2 with
            | childNil =>
                simp only [RawTermChildren.allStronglyNormalizing] at childrenSN
                exact piTyCode_isStronglyNormalizing_of_domain_codomain childrenSN.1 childrenSN.2.1
  · by_cases isSigma : generator = Generator.gen_sigmaTyCode
    · subst isSigma
      cases payload
      cases children with
      | childCons _domain rest =>
          cases rest with
          | childCons _codomain rest2 =>
              cases rest2 with
              | childNil =>
                  simp only [RawTermChildren.allStronglyNormalizing] at childrenSN
                  exact sigmaTyCode_isStronglyNormalizing_of_domain_codomain childrenSN.1 childrenSN.2.1
    · exfalso
      unfold typingRuleDescOf at isFormation
      rw [if_neg isPi, if_neg isSigma] at isFormation
      contradiction

mutual

/-- **Native subject strong normalization for the description formation engine (HT-A3), HasType-free.**  Every
formation-typed subject is strongly normalizing, proved on the formation engine's own structure rather than via
`HasTypeDesc.toHasType`: `var` / `universeFormation` are normal leaves; `conv` preserves the subject; the
`genFormation` former cell is SN once its telescope children are SN, discharged by
`formerCellStronglyNormalizingOfChildren` over the mutual telescope recursion.  The migration target the public
`HasTypeDesc.isStronglyNormalizing` delegates to. -/
theorem HasTypeDesc.subjectStronglyNormalizingNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    IsStronglyNormalizing subject :=
  match typed with
  | .var _context index =>
      isStronglyNormalizing_of_noStep (fun _ step => noStep_var index step)
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      HasTypeDesc.subjectStronglyNormalizingNative typedPremise
  | .universeFormation _context levelExpr flag =>
      isStronglyNormalizing_of_noStep (fun _ step => noStep_universeCode (levelExpr, flag) step)
  | .genFormation _context _generator _payload _children _levels _flag _rule isFormation premises =>
      formerCellStronglyNormalizingOfChildren isFormation
        (DescTelescope.childrenStronglyNormalizingNative premises)

/-- Every child of a formation telescope is strongly normalizing.  STANDALONE-shaped recursion on the
telescope but MUTUAL with the subject recursion: each head child's SN is `HasTypeDesc.subjectStronglyNormalizingNative`
of the head typing (a structural sub-derivation), and the rest accumulates recursively. -/
theorem DescTelescope.childrenStronglyNormalizingNative {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    children.allStronglyNormalizing :=
  match telescope with
  | .nil _ _ => True.intro
  | .cons _ _head _headLevel _restLevels _flag _rest headTyped restTyped =>
      ⟨HasTypeDesc.subjectStronglyNormalizingNative headTyped,
        DescTelescope.childrenStronglyNormalizingNative restTyped⟩

end

end FX1Poly.Typed

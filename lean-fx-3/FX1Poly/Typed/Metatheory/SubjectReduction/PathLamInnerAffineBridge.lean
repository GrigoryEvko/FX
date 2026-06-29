import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineCongruence
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/PathLamInnerAffineBridge — the typed ⟹ inner-affine bridge

The A1-SUBST-OPEN subterm-typing leg that discharges the residual of
`appScaledDimensionGrade_step_le_ofSitesAffine`: a typed body satisfies the structural invariant
`AllInnerPathLamAffine` (every `pathLam` subterm has an App-scaled-affine body).  The bridge is driven by
induction on `HasTypeUnion`, with the three table arms delegated to per-table CELL lemmas.

Each cell lemma concludes `AllInnerPathLamAffine (rule.memberCell scope args)` directly: in every
intro/elim/formation row each arg-child appears VERBATIM as an `obligation.subject` (the obligation list is a
superset of the cell's children — constructed terms appear only in classifiers/params/contexts), and
`AllInnerPathLamAffine` is a predicate on the subject term alone (context/classifier/scope-agnostic).  So the
per-obligation IH (`AllInner` on every obligation subject) reifies into `AllInnerPathLamAffineChildren` for the
actual children.  The `pathLam` intro row additionally reads its `sideCondition` (definitionally the
`bodyAffine` field) to land the `.pathLam` constructor. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal
open FX1Poly.Tier0.Syntax

/-- **The intro-table cell lemma.**  Under the per-obligation inner-affine IH (and, for `pathLam`, the row's
App-scaled affine `sideCondition`), every introducer member cell satisfies `AllInnerPathLamAffine`.  Sixteen
rows land `.other` (their head is not `gen_pathLam`, their children are exactly the args, each an obligation
subject); the `pathLam` row lands `.pathLam` from `sideHolds` (= `bodyAffine`) plus the body obligation's IH. -/
theorem introCellAffine {profile : PolyProfile} {scope : Nat}
    {generator : Generator} {rule : IntroRule}
    (isIntro : introRuleOf generator = some rule)
    (context : TypingContext profile scope)
    (args : RawTermChildren rule.argShifts scope)
    (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (sideHolds : rule.sideCondition scope args)
    (ihPremises : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffine (rule.memberCell scope args) := by
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil  -- boolTrue
  · exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil  -- boolFalse
  · exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil  -- unit
  · exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil  -- interval0
  · exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil  -- interval1
  · exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil  -- natZero
  · -- lam: args = [domainCode, body]; obligations = [domainCode, codomainCode(param), body]
    cases args with
    | childCons domainCode rest =>
      cases rest with
      | childCons body tail =>
        cases tail with
        | childNil =>
          cases params with
          | childCons codomainCode ptail =>
            cases ptail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide)
                (.cons (ihPremises _ (.head _))
                  (.cons (ihPremises _ (.tail _ (.tail _ (.head _)))) .nil))
  · -- pathLam: args = [body]; params = [carrierCode]; the sole survivor of the `.pathLam` constructor
    cases args with
    | childCons body tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons carrierCode ptail =>
          cases ptail with
          | childNil =>
            exact AllInnerPathLamAffine.pathLam sideHolds (ihPremises _ (.head _))
  · -- natSucc: args = [predecessor]; obligations = [predecessor]
    cases args with
    | childCons predecessor tail =>
      cases tail with
      | childNil =>
        exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)
  · -- listCons: args = [head, tail]; obligations = [head, tail]
    cases args with
    | childCons headValue rest =>
      cases rest with
      | childCons tailList tail =>
        cases tail with
        | childNil =>
          cases params with
          | childCons elementType ptail =>
            cases ptail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide)
                (.cons (ihPremises _ (.head _)) (.cons (ihPremises _ (.tail _ (.head _))) .nil))
  · -- optionSome: args = [value]; obligations = [value]
    cases args with
    | childCons value tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons typeParam0 ptail =>
          cases ptail with
          | childNil =>
            exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)
  · -- optionNone: args = []; obligations = [typeParam0(param)]
    exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil
  · -- listNil: args = []; obligations = [typeParam0(param)]
    exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil
  · -- eitherInl: args = [value]; obligations = [value, typeParam1(param), typeParam0(param)]
    cases args with
    | childCons value tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons typeParam0 prest =>
          cases prest with
          | childCons typeParam1 ptail =>
            cases ptail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)
  · -- eitherInr: args = [value]; obligations = [value, typeParam1(param), typeParam0(param)]
    cases args with
    | childCons value tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons typeParam0 prest =>
          cases prest with
          | childCons typeParam1 ptail =>
            cases ptail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)
  · -- pair: args = [child0, child1]; obligations = [child0, child1, typeParam0(param), typeParam1(param)]
    cases args with
    | childCons child0 rest =>
      cases rest with
      | childCons child1 tail =>
        cases tail with
        | childNil =>
          cases params with
          | childCons typeParam0 prest =>
            cases prest with
            | childCons typeParam1 ptail =>
              cases ptail with
              | childNil =>
                exact AllInnerPathLamAffine.other (by decide)
                  (.cons (ihPremises _ (.head _)) (.cons (ihPremises _ (.tail _ (.head _))) .nil))
  · -- refl: args = [witness]; obligations = [witness, typeParam0(param)]
    cases args with
    | childCons witness tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons typeParam0 ptail =>
          cases ptail with
          | childNil =>
            exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)

end FX1Poly.Typed

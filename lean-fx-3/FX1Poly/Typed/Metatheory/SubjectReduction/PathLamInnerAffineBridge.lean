import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineCongruence
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable

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

/-- **The elim-table cell lemma.**  Under the per-obligation inner-affine IH, every eliminator member cell
satisfies `AllInnerPathLamAffine`.  All eleven rows land `.other` (no eliminator head is `gen_pathLam`, and
`ElimRule` carries no `sideCondition`).  The member cell's children are the `args`; each arg appears as an
`obligation.subject`, but the cell's arg order generally differs from the obligation order (e.g. the recursors
list the scrutinee first while the cell lists the motive first), so the children's witnesses are read off the
matching obligation via `List.Mem` navigation. -/
theorem elimCellAffine {profile : PolyProfile} {scope : Nat}
    {generator : Generator} {rule : ElimRule}
    (isElim : elimRuleOf generator = some rule)
    (context : TypingContext profile scope)
    (args : RawTermChildren rule.argShifts scope)
    (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (ihPremises : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffine (rule.memberCell scope args) := by
  rcases elimRuleOf_cases isElim with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- app: cell [function, argument]; obligations [function@0, argument@1]
    cases args with
    | childCons function rest =>
      cases rest with
      | childCons argument tail =>
        cases tail with
        | childNil =>
          cases params with
          | childCons domainCode prest =>
            cases prest with
            | childCons codomainCode ptail =>
              cases ptail with
              | childNil =>
                exact AllInnerPathLamAffine.other (by decide)
                  (.cons (ihPremises _ (.head _)) (.cons (ihPremises _ (.tail _ (.head _))) .nil))
  · -- pathApp: cell [path, argument]; obligations [path@0, argument@1, carrierCode@2(param)]
    cases args with
    | childCons path rest =>
      cases rest with
      | childCons argument tail =>
        cases tail with
        | childNil =>
          cases params with
          | childCons carrierCode prest =>
            cases prest with
            | childCons leftEndpoint prest2 =>
              cases prest2 with
              | childCons rightEndpoint ptail =>
                cases ptail with
                | childNil =>
                  exact AllInnerPathLamAffine.other (by decide)
                    (.cons (ihPremises _ (.head _)) (.cons (ihPremises _ (.tail _ (.head _))) .nil))
  · -- natElim: cell [motive, base, step, scrutinee]; obligations [scrutinee@0, base@1, step@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons baseBranch rest2 =>
        cases rest2 with
        | childCons stepBranch rest3 =>
          cases rest3 with
          | childCons scrutinee tail =>
            cases tail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide)
                (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                  (.cons (ihPremises _ (.tail _ (.head _)))
                    (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                      (.cons (ihPremises _ (.head _)) .nil))))
  · -- natRec: cell [motive, base, step, scrutinee]; obligations [scrutinee@0, base@1, step@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons baseBranch rest2 =>
        cases rest2 with
        | childCons stepBranch rest3 =>
          cases rest3 with
          | childCons scrutinee tail =>
            cases tail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide)
                (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                  (.cons (ihPremises _ (.tail _ (.head _)))
                    (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                      (.cons (ihPremises _ (.head _)) .nil))))
  · -- boolElim: cell [motive, scrutinee, then, else]; obligations [scrutinee@0, then@1, else@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons scrutinee rest2 =>
        cases rest2 with
        | childCons thenBranch rest3 =>
          cases rest3 with
          | childCons elseBranch tail =>
            cases tail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide)
                (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                  (.cons (ihPremises _ (.tail _ (.head _)))
                    (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                      (.cons (ihPremises _ (.head _)) .nil))))
  · -- optionMatch: cell [motive, none, some, scrutinee]; obligations [scrutinee@0, none@1, some@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons noneBranch rest2 =>
        cases rest2 with
        | childCons someBranch rest3 =>
          cases rest3 with
          | childCons scrutinee tail =>
            cases tail with
            | childNil =>
              cases params with
              | childCons typeParamA prest =>
                cases prest with
                | childCons typeParamB ptail =>
                  cases ptail with
                  | childNil =>
                    exact AllInnerPathLamAffine.other (by decide)
                      (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                        (.cons (ihPremises _ (.tail _ (.head _)))
                          (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                            (.cons (ihPremises _ (.head _)) .nil))))
  · -- eitherMatch: cell [motive, left, right, scrutinee]; obligations [scrutinee@0, left@1, right@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons leftBranch rest2 =>
        cases rest2 with
        | childCons rightBranch rest3 =>
          cases rest3 with
          | childCons scrutinee tail =>
            cases tail with
            | childNil =>
              cases params with
              | childCons typeParamA prest =>
                cases prest with
                | childCons typeParamB ptail =>
                  cases ptail with
                  | childNil =>
                    exact AllInnerPathLamAffine.other (by decide)
                      (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                        (.cons (ihPremises _ (.tail _ (.head _)))
                          (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                            (.cons (ihPremises _ (.head _)) .nil))))
  · -- idJ: cell [motive, baseCase, witness]; obligations [witness@0, rightEndpoint@1(param), baseCase@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons baseCase rest2 =>
        cases rest2 with
        | childCons witness tail =>
          cases tail with
          | childNil =>
            cases params with
            | childCons typeCode prest =>
              cases prest with
              | childCons leftEndpoint prest2 =>
                cases prest2 with
                | childCons rightEndpoint ptail =>
                  cases ptail with
                  | childNil =>
                    exact AllInnerPathLamAffine.other (by decide)
                      (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                        (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                          (.cons (ihPremises _ (.head _)) .nil)))
  · -- fst: cell [pairTerm]; obligations [pairTerm@0, firstType@1(param)]
    cases args with
    | childCons pairTerm tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons firstType prest =>
          cases prest with
          | childCons secondType ptail =>
            cases ptail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)
  · -- snd: cell [pairTerm]; obligations [pairTerm@0, secondType@1(param)]
    cases args with
    | childCons pairTerm tail =>
      cases tail with
      | childNil =>
        cases params with
        | childCons firstType prest =>
          cases prest with
          | childCons secondType ptail =>
            cases ptail with
            | childNil =>
              exact AllInnerPathLamAffine.other (by decide) (.cons (ihPremises _ (.head _)) .nil)
  · -- listElim: cell [motive, scrutinee, nil, cons]; obligations [scrutinee@0, nil@1, cons@2, motive@3]
    cases args with
    | childCons motive rest =>
      cases rest with
      | childCons scrutinee rest2 =>
        cases rest2 with
        | childCons nilBranch rest3 =>
          cases rest3 with
          | childCons consBranch tail =>
            cases tail with
            | childNil =>
              cases params with
              | childCons elementType prest =>
                cases prest with
                | childCons resultType ptail =>
                  cases ptail with
                  | childNil =>
                    exact AllInnerPathLamAffine.other (by decide)
                      (.cons (ihPremises _ (.tail _ (.tail _ (.tail _ (.head _)))))
                        (.cons (ihPremises _ (.tail _ (.head _)))
                          (.cons (ihPremises _ (.tail _ (.tail _ (.head _))))
                            (.cons (ihPremises _ (.head _)) .nil))))

end FX1Poly.Typed

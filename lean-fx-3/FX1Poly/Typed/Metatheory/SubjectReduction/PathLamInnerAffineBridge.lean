import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineCongruence
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable
import FX1Poly.Typed.Engine.Union.HasTypeUnion

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
open FX1Poly.Axis.Syntax

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

/-! ## The formation-table cell lemma — navigation helpers

The `formationRule` arm's subject is `.mkGen formGenerator payload children` DIRECTLY (the formed type's
children, not rearranged args), with shifts `formGenerator.binderShifts`.  Pinning the generator makes those
shifts concrete, so `cases children` yields exactly the real spine and `.other` discharges the head-mismatch
(`formGenerator ≠ gen_pathLam`).  The flat / cumulative obligation lists depend on the `levels` list (zipped
positionally), so the head/tail obligation positions are read off after a short `cases levels`; both children
remain the obligation subjects at positions `0` and `1` regardless of which `levels` branch fires.  The
term-indexed obligations use the `level` and `carrier` PARAMS (not the `levels` list), so they need no
`cases levels`. -/

/-- **Flat binary-former children inner-affinity.**  Both children of a binary flat former
(`product`/`sum`/`either`/`arrow`/`equiv`, spine `[0, 0]`) are obligation subjects at positions `0`/`1` for
every `levels`; the obligation classifiers (the per-child universe codes) vary with `levels` but the subjects
do not.  The children are taken with the concrete `[0, 0]` shape so the cases pin the shifts and the
obligation list reduces. -/
theorem flatPairChildrenInner {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag}
    (children : RawTermChildren [0, 0] scope) (levels : List LevelExpr)
    (ihPremises : ∀ obligation ∈ flatFormationObligations profile context flag children levels,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffineChildren children := by
  cases children with
  | childCons head0 rest =>
      cases rest with
      | childCons head1 tail =>
          cases tail with
          | childNil =>
              cases levels with
              | nil =>
                  exact .cons (ihPremises _ (.head _)) (.cons (ihPremises _ (.tail _ (.head _))) .nil)
              | cons _ restLevels =>
                  cases restLevels with
                  | nil =>
                      exact .cons (ihPremises _ (.head _))
                        (.cons (ihPremises _ (.tail _ (.head _))) .nil)
                  | cons _ _ =>
                      exact .cons (ihPremises _ (.head _))
                        (.cons (ihPremises _ (.tail _ (.head _))) .nil)

/-- **Flat unary-former children inner-affinity.**  The single child of a unary flat modal former
(`ʃ`/`♭`/`♯`, spine `[0]`) is the obligation subject at position `0` for every `levels`. -/
theorem flatUnaryChildInner {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag}
    (children : RawTermChildren [0] scope) (levels : List LevelExpr)
    (ihPremises : ∀ obligation ∈ flatFormationObligations profile context flag children levels,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffineChildren children := by
  cases children with
  | childCons child tail =>
      cases tail with
      | childNil =>
          cases levels with
          | nil => exact .cons (ihPremises _ (.head _)) .nil
          | cons _ _ => exact .cons (ihPremises _ (.head _)) .nil

/-- **Cumulative binder-former children inner-affinity.**  The domain (spine head, ambient scope) and the
binder-crossing codomain (the head of the tail, at `scope + 1`) of a Π/Σ former (spine `[0, 1]`) are the
obligation subjects at positions `0`/`1` for every `levels` (`cumulativeBinderObligations`). -/
theorem cumulativeBinderChildrenInner {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag}
    (children : RawTermChildren [0, 1] scope) (levels : List LevelExpr)
    (ihPremises : ∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffineChildren children := by
  cases children with
  | childCons domain rest =>
      cases rest with
      | childCons codomain tail =>
          cases tail with
          | childNil =>
              cases levels with
              | nil =>
                  exact .cons (ihPremises _ (.head _)) (.cons (ihPremises _ (.tail _ (.head _))) .nil)
              | cons _ restLevels =>
                  cases restLevels with
                  | nil =>
                      exact .cons (ihPremises _ (.head _))
                        (.cons (ihPremises _ (.tail _ (.head _))) .nil)
                  | cons _ _ =>
                      exact .cons (ihPremises _ (.head _))
                        (.cons (ihPremises _ (.tail _ (.head _))) .nil)

/-- **Cumulative element-former children inner-affinity.**  The single element child of a List/Option former
(spine `[0]`) is the obligation subject at position `0` for every `levels`. -/
theorem cumulativeUnaryChildInner {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag}
    (children : RawTermChildren [0] scope) (levels : List LevelExpr)
    (ihPremises : ∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffineChildren children := by
  cases children with
  | childCons element tail =>
      cases tail with
      | childNil =>
          cases levels with
          | nil => exact .cons (ihPremises _ (.head _)) .nil
          | cons _ _ => exact .cons (ihPremises _ (.head _)) .nil

/-- **The formation-table cell lemma.**  Under the per-obligation inner-affine IH, every formed-type cell
satisfies `AllInnerPathLamAffine`.  Every formation generator's head is `≠ gen_pathLam` (`pathLam` is an
introducer, not a former), so the cell lands `.other`; its children are exactly the formed type's children,
each an obligation subject, so the IH reifies into `AllInnerPathLamAffineChildren` via the per-family
navigation helpers.  Dispatch is `cases rule` (the four formation families) then a per-generator pin so the
children spine is concrete; the family fallthrough is impossible by the family's reverse extraction. -/
theorem formationCellAffine {profile : PolyProfile} {scope : Nat}
    {formGenerator : Generator} {rule : FormationRule}
    (isFormationRule : formationRuleOf formGenerator = some rule)
    {context : TypingContext profile scope}
    (payload : formGenerator.payload scope)
    (children : RawTermChildren formGenerator.binderShifts scope)
    (levels : List LevelExpr) (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (ihPremises : ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      AllInnerPathLamAffine obligation.subject) :
    AllInnerPathLamAffine (.mkGen formGenerator payload children) := by
  cases rule with
  | baseType baseRule =>
      -- Base-type formers are nullary (`binderShifts = []`); pin the generator so `children = childNil`.
      have baseHit := formationRuleOf_baseType_inv isFormationRule
      by_cases hBool : formGenerator = .gen_boolCode
      · subst hBool; cases children with
        | childNil => exact .other (by decide) .nil
      · by_cases hEmpty : formGenerator = .gen_emptyCode
        · subst hEmpty; cases children with
          | childNil => exact .other (by decide) .nil
        · by_cases hNat : formGenerator = .gen_natCode
          · subst hNat; cases children with
            | childNil => exact .other (by decide) .nil
          · by_cases hUnit : formGenerator = .gen_unitCode
            · subst hUnit; cases children with
              | childNil => exact .other (by decide) .nil
            · by_cases hInterval : formGenerator = .gen_intervalCode
              · subst hInterval; cases children with
                | childNil => exact .other (by decide) .nil
              · exfalso
                simp only [baseTypeRuleDescOf, if_neg hBool, if_neg hEmpty, if_neg hNat, if_neg hUnit,
                  if_neg hInterval] at baseHit
                injection baseHit
  | flat flatRule =>
      have flatHit := formationRuleOf_flat_inv isFormationRule
      by_cases hProduct : formGenerator = .gen_productCode
      · subst hProduct; exact .other (by decide) (flatPairChildrenInner children levels ihPremises)
      · by_cases hSum : formGenerator = .gen_sumCode
        · subst hSum; exact .other (by decide) (flatPairChildrenInner children levels ihPremises)
        · by_cases hEither : formGenerator = .gen_eitherCode
          · subst hEither; exact .other (by decide) (flatPairChildrenInner children levels ihPremises)
          · by_cases hArrow : formGenerator = .gen_arrowCode
            · subst hArrow; exact .other (by decide) (flatPairChildrenInner children levels ihPremises)
            · by_cases hEquiv : formGenerator = .gen_equivCode
              · subst hEquiv; exact .other (by decide) (flatPairChildrenInner children levels ihPremises)
              · by_cases hShape : formGenerator = .gen_shapeModality
                · subst hShape; exact .other (by decide) (flatUnaryChildInner children levels ihPremises)
                · by_cases hFlat : formGenerator = .gen_flatModality
                  · subst hFlat; exact .other (by decide) (flatUnaryChildInner children levels ihPremises)
                  · by_cases hSharp : formGenerator = .gen_sharpModality
                    · subst hSharp
                      exact .other (by decide) (flatUnaryChildInner children levels ihPremises)
                    · exfalso
                      simp only [flatTypingRuleDescOf, if_neg hProduct, if_neg hSum, if_neg hEither,
                        if_neg hArrow, if_neg hEquiv, if_neg hShape, if_neg hFlat, if_neg hSharp] at flatHit
                      injection flatHit
  | termIndexed termRule =>
      -- Term-indexed formers (`id`/`bridge`, spine `[0, 0, 0]`): carrier child + two endpoints, all obligation
      -- subjects (the obligations use the `level`/`carrier` params, not the `levels` list).
      have termHit := formationRuleOf_termIndexed_inv isFormationRule
      by_cases hBridge : formGenerator = .gen_bridgeCode
      · subst hBridge; cases children with
        | childCons carrierChild rest => cases rest with
          | childCons leftEndpoint rest2 => cases rest2 with
            | childCons rightEndpoint tail => cases tail with
              | childNil =>
                exact .other (by decide)
                  (.cons (ihPremises _ (.head _))
                    (.cons (ihPremises _ (.tail _ (.head _)))
                      (.cons (ihPremises _ (.tail _ (.tail _ (.head _)))) .nil)))
      · by_cases hId : formGenerator = .gen_idCode
        · subst hId; cases children with
          | childCons carrierChild rest => cases rest with
            | childCons leftEndpoint rest2 => cases rest2 with
              | childCons rightEndpoint tail => cases tail with
                | childNil =>
                  exact .other (by decide)
                    (.cons (ihPremises _ (.head _))
                      (.cons (ihPremises _ (.tail _ (.head _)))
                        (.cons (ihPremises _ (.tail _ (.tail _ (.head _)))) .nil)))
        · exfalso
          simp only [termIndexedFormerDescOf, if_neg hBridge, if_neg hId] at termHit
          injection termHit
  | cumulative cumulativeRule =>
      have cumulativeHit := formationRuleOf_cumulative_inv isFormationRule
      by_cases hPi : formGenerator = .gen_piTyCode
      · subst hPi; exact .other (by decide) (cumulativeBinderChildrenInner children levels ihPremises)
      · by_cases hSigma : formGenerator = .gen_sigmaTyCode
        · subst hSigma
          exact .other (by decide) (cumulativeBinderChildrenInner children levels ihPremises)
        · by_cases hList : formGenerator = .gen_listCode
          · subst hList; exact .other (by decide) (cumulativeUnaryChildInner children levels ihPremises)
          · by_cases hOption : formGenerator = .gen_optionCode
            · subst hOption
              exact .other (by decide) (cumulativeUnaryChildInner children levels ihPremises)
            · exfalso
              -- `gen_unitCode` is the only other cumulative hit, but it is a `baseType` row (tried first),
              -- so `formationRuleOf` never tags it `.cumulative`.  The remaining generators miss the
              -- cumulative table outright.
              simp only [typingRuleDescOf, if_neg hPi, if_neg hSigma, if_neg hList, if_neg hOption]
                at cumulativeHit
              by_cases hUnit : formGenerator = .gen_unitCode
              · -- `gen_unitCode` resolves to a `.baseType` row (`formationRuleOf` tries base types first),
                -- so the `.cumulative` tag in `isFormationRule` is impossible.
                subst hUnit
                rw [show formationRuleOf Generator.gen_unitCode
                      = some (FormationRule.baseType
                          { outputUniverse := fun _ =>
                              universeCodeCell LevelExpr.lzero UniverseFlag.standard })
                      from rfl] at isFormationRule
                injection isFormationRule with headEq
                injection headEq
              · rw [if_neg hUnit] at cumulativeHit
                injection cumulativeHit

/-- **★ The typed ⟹ inner-affine bridge (A1-SUBST-OPEN subterm-typing leg).**  A union-typed subject
satisfies the structural invariant `AllInnerPathLamAffine` — every `pathLam` subterm has an App-scaled-affine
body.  By induction on the derivation: the three table arms delegate to their CELL lemmas
(`formationCellAffine` / `introCellAffine` / `elimCellAffine`), reading each per-obligation IH; the `conv` arm
preserves the subject (its IH applies directly); the structural leaves `var` / `universeFormation` land
`.other` (their heads `gen_var` / `gen_universeCode` are `≠ gen_pathLam`, and they are childless).  This is
exactly the residual that `appScaledDimensionGrade_step_le_ofSitesAffine` isolated — that a TYPED `pathLam`
body's inner `pathLam` sites are all affine — discharged here from typing structurally (every inner `pathLam`
is itself an `intro` whose `sideCondition` IS the App-scaled affine grade). -/
theorem allInnerPathLamAffine_ofTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier) :
    AllInnerPathLamAffine subject := by
  induction derivation with
  | formationRule armContext generator payload children rule levels carrier level flag
      isFormationRule _premisesHold _usabilityHolds ihPremises =>
      exact formationCellAffine isFormationRule payload children levels carrier level flag ihPremises
  | intro armContext generator rule args params level0 level1 flag isIntro sideHolds
      _premisesHold _usabilityHolds ihPremises =>
      exact introCellAffine isIntro armContext args params level0 level1 flag sideHolds ihPremises
  | elim armContext generator rule args params level0 level1 flag isElim
      _premisesHold _usabilityHolds ihPremises =>
      exact elimCellAffine isElim armContext args params level0 level1 flag ihPremises
  | conv _levelExpr _flag _typed _converts _reclassifierTyped typedIH _reclassifierIH =>
      exact typedIH
  | var _armContext _index _isAccessible =>
      exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil
  | universeFormation _armContext _levelExpr _flag =>
      exact AllInnerPathLamAffine.other (by decide) AllInnerPathLamAffineChildren.nil

end FX1Poly.Typed

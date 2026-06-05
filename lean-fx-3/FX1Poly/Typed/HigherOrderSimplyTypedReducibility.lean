import FX1Poly.Typed.FirstOrderSimplyTypedReducibility

/-! # FX1Poly/Typed/HigherOrderSimplyTypedReducibility
    — Tait reducibility + member-extension for the FULL higher-order simply-typed fragment

**OFF-PATH CROSSCHECK (supersession map, 2026-06-05): ROUTE-A all-level fragment (extends
`FirstOrderSimplyTypedReducibility`'s #672 member-extension to higher-order domains).  Off the kernel critical
path — the BFT bounded route closed SN-043 without the all-level member-extension principle.  Retained as a
crosscheck.**

`FirstOrderSimplyTypedReducibility` proved the universe member-extension principle for the FIRST-ORDER
simply-typed fragment: neutral/data leaves and non-dependent arrows whose DOMAIN is a leaf (curried
first-order functions `A₁ → … → Aₙ → B` over base types).  Its `arrow` constructor restricts the domain to a
leaf (`domainNotPiType`), and its docstring states higher-order domains `(A → B) → C` "hit the open fuel-`0`
wall".  That is OVERLY CONSERVATIVE: it conflates an ARROW domain with a UNIVERSE domain.  Only a universe
domain genuinely hits the wall (its member-extension is the open type-polymorphic core); an arrow domain's
reducibility and member-extension are supplied RECURSIVELY by the structural induction hypothesis, with no
appeal to the universe member-extension.

`IsSimplyTyped` is the full simply-typed fragment: neutral/data leaves closed under non-dependent arrow on
BOTH the domain and the codomain — i.e. every simple type built from neutral/data base types with arbitrary
arrow nesting, the genuine simply-typed lambda calculus (STLC).  `reducibleAndMemberExtension` proves the
classic Tait result (all-levels type reducibility ∧ positive member-extension) for it, by structural
induction on the witness.

## Why the recursion closes (and exactly what unblocked it)

The `arrow` case (domain `D` simply-typed, codomain `C` simply-typed, type `D → C`):

  * TYPE side — `IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain` (the member-extension-FREE
    non-dependent arrow): the type-leg of `D → C` needs only `D` and `C` reducible at all levels, supplied
    by the two induction hypotheses.  This is the lemma that removed the any-level domain member-extension
    requirement the recursive IH could not supply (the IH gives only POSITIVE-source member-extension), so
    it is precisely what makes the arrow-domain recursion go through.
  * MEMBER side — `IsReducibleMemberAtAllPositiveLevels.nonDependentArrowPositive`: its domain/codomain
    member-extension premises are POSITIVE-source (`memberPredLevel + 1`), exactly the shape the IH's
    member-extension half delivers — for a leaf via `ofNeutralClassifier`, for an arrow domain via the
    recursive IH.  No appeal to the open universe member-extension.

So the arrow-domain case recurses with no new obstruction; the wall is genuinely confined to UNIVERSE
domains and DEPENDENT codomains, neither of which appears in a simple type over neutral/data base types.

## Zero-axiom verification

`induction simplyTyped` with the leaf arm (`ofWeakHeadNormalNonPiNonUniverse` + `ofNeutralClassifier`) and
the arrow arm (the two lemmas above fed the domain/codomain induction hypotheses).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Higher-order simply-typed witness.**  A type is simply-typed when it is either a neutral / data former
(a `leaf`: weak-head-normal, not Π-, not universe-rooted) or a non-dependent `arrow` whose DOMAIN and
codomain are themselves simply-typed.  Unlike `IsFirstOrderSimplyTyped`, the domain need NOT be a leaf — it
may itself be an arrow, so this captures the full simply-typed lambda calculus `(A → B) → C → …` over
neutral / data base types.  Universe domains stay excluded (no universe constructor, and a universe code
fails the leaf's `notUniverse` condition): their member-extension is the open type-polymorphic core. -/
inductive IsSimplyTyped : {scope : Nat} → RawTerm scope → Prop
  | leaf {scope : Nat} {classifier : RawTerm scope}
      (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
      (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
      (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode) :
      IsSimplyTyped classifier
  | arrow {scope : Nat} {domainCode codomainBase : RawTerm scope}
      (domainSimplyTyped : IsSimplyTyped domainCode)
      (codomainSimplyTyped : IsSimplyTyped codomainBase) :
      IsSimplyTyped (piTyCodeCell domainCode (RawTerm.weaken codomainBase))

/-- **The universe member-extension principle, proved for the FULL higher-order simply-typed fragment.**
Every simply-typed type is reducible at all levels AND admits member-extension (a member at one positive
source level is a member at every positive level) — the classic Tait reducibility result for the simply-typed
lambda calculus over neutral / data base types.  Structural induction: the leaf arm is the neutral/data leaf;
the arrow arm feeds the domain and codomain induction hypotheses to the member-extension-free type-side arrow
(`nonDependentArrowOfAllLevelsDomain`) and the positive-source member-side arrow
(`nonDependentArrowPositive`).  Strictly generalizes `IsFirstOrderSimplyTyped.reducibleAndMemberExtension`
(see `IsSimplyTyped.ofFirstOrder`). -/
theorem IsSimplyTyped.reducibleAndMemberExtension {scope : Nat} {typeCode : RawTerm scope}
    (simplyTyped : IsSimplyTyped typeCode) :
    IsReducibleTypeAtAllLevels typeCode ∧
      (∀ (term : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) typeCode term →
          IsReducibleMemberAtAllPositiveLevels typeCode term) := by
  induction simplyTyped with
  | leaf weakHeadNormal notPiType notUniverse =>
      exact ⟨IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          weakHeadNormal notPiType notUniverse,
        fun term {_predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
            weakHeadNormal notPiType notUniverse member⟩
  | arrow _domainSimplyTyped _codomainSimplyTyped domainInductiveHypothesis codomainInductiveHypothesis =>
      obtain ⟨domainAllLevels, domainMemberExtension⟩ := domainInductiveHypothesis
      obtain ⟨codomainAllLevels, codomainMemberExtension⟩ := codomainInductiveHypothesis
      refine ⟨IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain
          domainAllLevels codomainAllLevels,
        fun functionTerm {predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.nonDependentArrowPositive domainAllLevels
            (fun argument {_memberPredLevel} memberArgument => domainMemberExtension argument memberArgument)
            codomainAllLevels
            (fun applicationTerm {_memberPredLevel} memberApplication =>
              codomainMemberExtension applicationTerm memberApplication)
            member⟩

/-- **Every first-order simply-typed type is simply-typed.**  The leaf-domain `arrow` of
`IsFirstOrderSimplyTyped` is the `IsSimplyTyped.arrow` whose domain is a leaf — so the first-order fragment
embeds into the higher-order one, witnessing that `IsSimplyTyped` is a strict generalization. -/
theorem IsSimplyTyped.ofFirstOrder {scope : Nat} {typeCode : RawTerm scope}
    (firstOrder : IsFirstOrderSimplyTyped typeCode) : IsSimplyTyped typeCode := by
  induction firstOrder with
  | leaf weakHeadNormal notPiType notUniverse =>
      exact IsSimplyTyped.leaf weakHeadNormal notPiType notUniverse
  | arrow domainWeakHeadNormal domainNotPiType domainNotUniverse _codomainFirstOrder codomainSimplyTyped =>
      exact IsSimplyTyped.arrow
        (IsSimplyTyped.leaf domainWeakHeadNormal domainNotPiType domainNotUniverse)
        codomainSimplyTyped

/-- **Every neutral type is simply-typed** (the general leaf, mirroring `IsFirstOrderSimplyTyped.ofNeutral`):
a neutral term — variable, neutral application, projection, stuck eliminator — is weak-head-normal and rooted
at an elimination generator, hence an `IsSimplyTyped` leaf. -/
theorem IsSimplyTyped.ofNeutral {scope : Nat} {classifier : RawTerm scope}
    (neutral : IsNeutral classifier) : IsSimplyTyped classifier :=
  IsSimplyTyped.leaf
    neutral.noWeakHeadStep
    neutral.rootGenerator_ne_piTyCode
    neutral.rootGenerator_ne_universeCode

/-- **A genuinely HIGHER-ORDER type is simply-typed: `(A → B) → C` over neutral base types.**  The domain
`A → B` is itself an arrow (NOT a leaf), so this type lies strictly OUTSIDE `IsFirstOrderSimplyTyped` (whose
`arrow` forbids a Π-rooted domain).  It witnesses that the higher-order fragment is non-empty and properly
contains the first-order one. -/
theorem IsSimplyTyped.higherOrderArrow {scope : Nat} {baseA baseB baseC : RawTerm scope}
    (neutralA : IsNeutral baseA) (neutralB : IsNeutral baseB) (neutralC : IsNeutral baseC) :
    IsSimplyTyped
      (piTyCodeCell (piTyCodeCell baseA (RawTerm.weaken baseB)) (RawTerm.weaken baseC)) :=
  IsSimplyTyped.arrow
    (IsSimplyTyped.arrow (IsSimplyTyped.ofNeutral neutralA) (IsSimplyTyped.ofNeutral neutralB))
    (IsSimplyTyped.ofNeutral neutralC)

/-- **End-to-end on the higher-order type `(A → B) → C`: reducible at all levels and member-extending.**  The
Tait assembly applied to `higherOrderArrow` — concretely exercising reducibility + member-extension on a type
with an ARROW domain, the ground newly covered beyond the first-order fragment. -/
theorem IsSimplyTyped.higherOrderArrowReducibleAndMemberExtension {scope : Nat}
    {baseA baseB baseC : RawTerm scope}
    (neutralA : IsNeutral baseA) (neutralB : IsNeutral baseB) (neutralC : IsNeutral baseC) :
    IsReducibleTypeAtAllLevels
        (piTyCodeCell (piTyCodeCell baseA (RawTerm.weaken baseB)) (RawTerm.weaken baseC)) ∧
      (∀ (term : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1)
            (piTyCodeCell (piTyCodeCell baseA (RawTerm.weaken baseB)) (RawTerm.weaken baseC)) term →
          IsReducibleMemberAtAllPositiveLevels
            (piTyCodeCell (piTyCodeCell baseA (RawTerm.weaken baseB)) (RawTerm.weaken baseC)) term) :=
  (IsSimplyTyped.higherOrderArrow neutralA neutralB neutralC).reducibleAndMemberExtension

/-- **The simply-typed discharge of the #672 member-extension principle, in operational form.**  For ANY
simply-typed type code (`IsSimplyTyped`), a member at one positive source level extends to every positive
level — the `IsReducibleMemberAtAllPositiveLevels` half of `reducibleAndMemberExtension`, projected to the
exact operational shape of `HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` (#672).  This is
the predicative STLC dispatch arm of the eventual #672 assembly, discharged in full generality (no `predLevel`
fixed, any simply-typed type): the simply-typed cases need neither the `IsStronglyNormalizing` nor the
`IsReducibleTypeAtAllLevels` hypothesis of #672 — both are CONCLUSIONS of simply-typedness
(`reducibleAndMemberExtension.1`).  The genuine open residual is everything OUTSIDE this fragment: Π types with
a UNIVERSE domain (the impredicative type-polymorphic core) and DEPENDENT codomains (where `subst0` preserves
the codomain's root generator but NOT, in general, its weak-head-normality — a head redex can appear when the
binder occupied an eliminator position). The general witnesses (`ofNeutral` / `ofFirstOrder` /
`higherOrderArrow`) all factor through this lemma. -/
theorem IsSimplyTyped.positiveMemberExtension {scope : Nat} {typeCode term : RawTerm scope}
    {predLevel : Nat} (simplyTyped : IsSimplyTyped typeCode)
    (member : IsReducibleMemberAt (predLevel + 1) typeCode term) :
    IsReducibleMemberAtAllPositiveLevels typeCode term :=
  (simplyTyped.reducibleAndMemberExtension).2 term member

end FX1Poly.Typed

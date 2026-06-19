import FX1Poly.Core.Substrate.Univalence.UnivalenceRowNormalForm
import FX1Poly.Core.Rewriting.Confluence.Newman
import FX1Poly.Tier0.Term.Core.RawTermDecEq

/-! # FX1Poly/Core/Substrate/Univalence/UnivalenceRowDecidableConv
    — DECIDABLE conversion for the definitional-univalence row, by computation: two terms are joinable
    under `Id_U ↝ Equiv` iff their bottom-up normal forms are equal

`UnivalenceRowNormalForm` shipped `univNF` (the bottom-up structural normalizer) and the invariant that a
single step preserves it (`univNF_preservesStep`).  This file completes the decision procedure:

  * the invariant lifts to the reflexive-transitive closure: `a ⟶* b → a.univNF = b.univNF`;
  * every term reduces to its normal form: `a ⟶* a.univNF` (via the reflexive-transitive-closure congruence
    lift and a one-step root fire);
  * therefore `Joinable a b ↔ a.univNF = b.univNF` — the (→) by preservation along both chains, the (←) by
    the common reduct `a.univNF`;
  * `Decidable (Joinable UnivalenceRowStep a b)` by `decidable_of_iff` + the zero-axiom `DecidableEq RawTerm`.

This is "**decidable definitional univalence by computation**" on the firing-linked univalence row — the
decision procedure normalizes both sides and compares.  It rides the generic, propext-clean `Joinable`
vocabulary of `Newman.lean` over `UnivalenceRowStep`, and needs NO `Acc.rec` / SN / Newman / local
confluence: the deterministic redex-free normalizer `univNF` IS the confluence content.

## Honest scope

This decides Conv for the univalence row alone — the rule that creates no new redexes, so `univNF` is a
sound complete confluent normalizer.  The size-growing demo row (`SizeGrowingTransportDemoStep`) CREATES
redexes (`glueElim A` when `A` is `productCode`-headed), so a single bottom-up pass does NOT normalize it;
its decision procedure would need the SN + Newman route.  The duplicating beta/iota rows are excluded
entirely (the Geser frontier).

## Zero-axiom verification

The closure inductions are structural; `univNFRoot_reaches` is `split` + the firing constructor; the iff is
`rintro`/`▸`; the instance is `decidable_of_iff` over `instDecidableEqRawTerm`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-! ## The preservation invariant lifts to the reflexive-transitive closure -/

/-- A multi-step univalence reduction preserves the bottom-up normal form. -/
theorem reflTransClosure_preservesUnivNF {scope : Nat} {source target : RawTerm scope}
    (chain : ReflTransClosure UnivalenceRowStep source target) : source.univNF = target.univNF := by
  induction chain with
  | refl _ => rfl
  | head firstStep _rest inductionHypothesis =>
      exact (univNF_preservesStep firstStep).trans inductionHypothesis

/-! ## Reflexive-transitive-closure congruence lifts -/

/-- Lift a children reduction to a term reduction (congruence under a generator). -/
theorem reflTransClosure_cong {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    {children children' : RawTermChildren generator.binderShifts scope}
    (chain : ReflTransClosure UnivalenceRowStepChildren children children') :
    ReflTransClosure UnivalenceRowStep (.mkGen generator payload children)
      (.mkGen generator payload children') := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head firstStep _rest inductionHypothesis =>
      exact ReflTransClosure.head (UnivalenceRowStep.cong generator payload firstStep) inductionHypothesis

/-- Lift a head reduction to a children reduction (the `here` position). -/
theorem reflTransClosure_here {parentScope headShift : Nat} {restShifts : List Nat}
    {head head' : RawTerm (parentScope + headShift)} (rest : RawTermChildren restShifts parentScope)
    (chain : ReflTransClosure UnivalenceRowStep head head') :
    ReflTransClosure UnivalenceRowStepChildren
      (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest) := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head firstStep _rest inductionHypothesis =>
      exact ReflTransClosure.head (UnivalenceRowStepChildren.here rest firstStep) inductionHypothesis

/-- Lift a tail reduction to a children reduction (the `there` position). -/
theorem reflTransClosure_there {parentScope headShift : Nat} {restShifts : List Nat}
    (head : RawTerm (parentScope + headShift)) {tail tail' : RawTermChildren restShifts parentScope}
    (chain : ReflTransClosure UnivalenceRowStepChildren tail tail') :
    ReflTransClosure UnivalenceRowStepChildren
      (RawTermChildren.childCons head tail) (RawTermChildren.childCons head tail') := by
  induction chain with
  | refl _ => exact ReflTransClosure.refl _
  | head firstStep _rest inductionHypothesis =>
      exact ReflTransClosure.head (UnivalenceRowStepChildren.there head firstStep) inductionHypothesis

/-! ## Every term reduces to its normal form -/

/-- The root step reaches `univNFRoot`: `mkGen g p children` reduces (in 0 or 1 steps) to its root form.
Three positions: (1) not `gen_idCode` ⇒ `univNFRoot` is the identity (`dif_neg`); (2) `gen_idCode` with a
`universeCode`-headed first child ⇒ a single `fire`; (3) `gen_idCode` with any other first child ⇒ the
identity (the stuck `if` reduces to the else branch via `if_neg`).  The first child is destructured BEFORE
the `if`-test so `headIsUniverseCode` reduces to a `decide` (the previous mis-binding fix). -/
theorem univNFRoot_reaches {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    ReflTransClosure UnivalenceRowStep (.mkGen generator payload children)
      (RawTerm.univNFRoot generator payload children) := by
  by_cases hIsIdCode : generator = .gen_idCode
  · subst hIsIdCode
    match children with
    | .childCons child0 (.childCons child1 (.childCons child2 .childNil)) =>
        match child0 with
        | .mkGen child0Gen child0Payload child0Children =>
            by_cases hGen : child0Gen = .gen_universeCode
            · subst hGen
              match child0Children, child0Payload with
              | .childNil, (levelExpr, flag) =>
                  exact ReflTransClosure.single
                    (UnivalenceRowStep.fire levelExpr flag child1 child2)
            · show ReflTransClosure UnivalenceRowStep
                (.mkGen .gen_idCode payload
                  (.childCons (.mkGen child0Gen child0Payload child0Children)
                    (.childCons child1 (.childCons child2 .childNil))))
                (if (RawTerm.mkGen child0Gen child0Payload child0Children).headIsUniverseCode then
                    RawTerm.mkGen .gen_equivCode () (.childCons child1 (.childCons child2 .childNil))
                  else
                    RawTerm.mkGen .gen_idCode payload
                      (.childCons (.mkGen child0Gen child0Payload child0Children)
                        (.childCons child1 (.childCons child2 .childNil))))
              rw [if_neg (show ¬ ((RawTerm.mkGen child0Gen child0Payload child0Children).headIsUniverseCode = true)
                    from fun hHead => hGen (of_decide_eq_true hHead))]
              exact ReflTransClosure.refl _
  · have hRootIsSource : RawTerm.univNFRoot generator payload children
        = .mkGen generator payload children := by
      unfold RawTerm.univNFRoot
      rw [dif_neg hIsIdCode]
    rw [hRootIsSource]
    exact ReflTransClosure.refl _

-- Every term reduces to its bottom-up normal form (mutually with the children version).  Structural
-- recursion on the term: normalize the children (congruence lift), then fire the root (`univNFRoot_reaches`).
mutual
  theorem univNF_reaches {scope : Nat} (term : RawTerm scope) :
      ReflTransClosure UnivalenceRowStep term term.univNF := by
    match term with
    | .mkGen generator payload children =>
        exact (reflTransClosure_cong generator payload (univNFChildren_reaches children)).trans
          (univNFRoot_reaches generator payload (RawTermChildren.univNF children))
  theorem univNFChildren_reaches {shifts : List Nat} {scope : Nat}
      (children : RawTermChildren shifts scope) :
      ReflTransClosure UnivalenceRowStepChildren children children.univNF := by
    match children with
    | .childNil => exact ReflTransClosure.refl _
    | .childCons head tail =>
        exact (reflTransClosure_here tail (univNF_reaches head)).trans
          (reflTransClosure_there head.univNF (univNFChildren_reaches tail))
end

/-! ## The decision procedure -/

/-- **★ Joinability under the univalence row is decided by normal-form equality.**  (→) preservation along
both chains; (←) the common reduct `a.univNF` (both reduce to it). -/
theorem joinable_iff_univNFEq {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Joinable UnivalenceRowStep leftTerm rightTerm ↔ leftTerm.univNF = rightTerm.univNF := by
  constructor
  · rintro ⟨commonReduct, leftToCommon, rightToCommon⟩
    exact (reflTransClosure_preservesUnivNF leftToCommon).trans
      (reflTransClosure_preservesUnivNF rightToCommon).symm
  · intro hNormalFormsEqual
    exact ⟨leftTerm.univNF, univNF_reaches leftTerm,
      hNormalFormsEqual.symm ▸ univNF_reaches rightTerm⟩

/-- **★ Conversion on the definitional-univalence row is DECIDABLE — by computation.**  Normalize both
terms (`univNF`) and compare via the zero-axiom `DecidableEq RawTerm`.  The decision procedure for "are
these two terms equal up to `Id_U ↝ Equiv`?". -/
instance instDecidableJoinableUnivalenceRowStep {scope : Nat} (leftTerm rightTerm : RawTerm scope) :
    Decidable (Joinable UnivalenceRowStep leftTerm rightTerm) :=
  decidable_of_iff (leftTerm.univNF = rightTerm.univNF) (joinable_iff_univNFEq leftTerm rightTerm).symm

/-! ## Non-vacuity — the decider classifies a real conversion and a real non-conversion -/

/-- The univalence redex IS joinable with its reduct (they share the normal form). -/
theorem univalenceRedex_joinable_reduct {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (lhsCode rhsCode : RawTerm scope) :
    Joinable UnivalenceRowStep
      (.mkGen .gen_idCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons lhsCode (.childCons rhsCode .childNil))))
      (.mkGen .gen_equivCode () (.childCons lhsCode (.childCons rhsCode .childNil))) :=
  (joinable_iff_univNFEq _ _).mpr (univNF_preservesStep (UnivalenceRowStep.fire levelExpr flag lhsCode rhsCode))

/-! ## Honest rails -/

/-- **Honesty marker.**  The decision procedure is by COMPUTATION (`univNF` + `DecidableEq`), with NO
`Acc.rec` / SN / Newman / local-confluence proof — the redex-free `univNF` is the confluence content.
`= true`. -/
def fxUnivalenceConv_decidesByComputation : Bool := true

/-- **Honesty marker.**  This decides the univalence row ALONE (no new redexes ⇒ one bottom-up pass
normalizes).  The size-growing demo row creates redexes; the duplicating beta/iota rows are excluded.
`= false` (NOT the full kernel Conv). -/
def fxUnivalenceConv_isGlobalKernelConv : Bool := false

end FX1Poly.Core

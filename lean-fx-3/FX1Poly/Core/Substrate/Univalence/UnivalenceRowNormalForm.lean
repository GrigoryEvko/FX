import FX1Poly.Core.Substrate.Univalence.DefinitionalUnivalenceRowSN

/-! # FX1Poly/Core/Substrate/Univalence/UnivalenceRowNormalForm

    TODO REFACTOR (ship over tables as data) — BESPOKE scaffolding: a hand-rolled
    inductive rewrite relation + hand proofs.  Target = TABLE DATA: univalence is
    ALREADY the row `univalenceShapedDemoRule`; the size-growing transport rule needs
    its own `IotaRuleDesc` row (nested `builtGen`, expressible).  Over `StepOverTable`
    the reducer / soundness / completeness / `normalizeOverTable` / confluence
    (`StepOverTable.confluent` via a `rfl` `WfIotaTable`) /
    `ConvOverTable.decidableOfStronglyNormalizing` are ALL generic; the ONLY bespoke
    residue is the size-growing row's SN — a `productFormerCount` measure-decrease lemma
    over `StepOverTable` fed to the generic `wellFounded_of_natMeasureStrictlyDecreasing`
    (SN as data on the row).
    — the bottom-up structural normal form for the definitional-univalence row, and the invariant that a
    single univalence step preserves it (confluence, made computable, with NO Acc.rec / SN / Newman)

The univalence rewrite `idCode(universeCode, A, B) ↝ equivCode(A, B)` CREATES NO new redexes: the reduct
head `equivCode` is inert (no rule fires on it) and `A`, `B` are carried unchanged.  So the bottom-up
structural normal form `univNF` (normalize the children, then fire the root ONCE if it is now an
`idCode(universeCode, _, _)`) is a TOTAL STRUCTURAL function — and a single univalence step PRESERVES it:
`UnivalenceRowStep a b → a.univNF = b.univNF`.  That invariant is confluence in computable form: any two
joinable terms have the same `univNF`, with no well-founded recursion, no Newman, no local-confluence proof.

## What this ships

  * `RawTerm.univNF` / `RawTermChildren.univNF` — the bottom-up structural normalizer; the root fires when
    the node is `idCode` with a `universeCode`-headed first child (total structural recursion — no `Acc`/SN).
  * **`univNF_preservesStep` (★)** — a single univalence step preserves `univNF` (mutual structural
    recursor; `fire` by the firing characterization, congruence by the inductive hypothesis).  The
    confluence invariant.

## Zero-axiom verification

`univNF` is plain structural recursion; the root guard is `dite`/`if` over `DecidableEq Generator`
(propext-clean — the `Generator.hasRedexHead` pattern, no match-wildcard over the generator enum); the
preservation is the explicit mutual recursor over an EQUALITY motive with `congrArg`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

/-! ## The bottom-up structural normalizer -/

/-- Is this term's head `gen_universeCode`?  A decidable head test (`decide`-of-`DecidableEq`, no
match-wildcard over the generator enum). -/
def RawTerm.headIsUniverseCode {scope : Nat} : RawTerm scope → Bool
  | .mkGen generator _payload _children => decide (generator = .gen_universeCode)

/-- The root step of the normalizer: if the (already-children-normalized) node is an `idCode` whose first
child is `universeCode`-headed, fire the univalence rule (`equivCode` of the second and third children);
otherwise leave the node as is.  The `generator = gen_idCode` guard is a `dite` over `DecidableEq Generator`,
so the dependent spine retype is propext-clean; the spine match is the single exhaustive 3-child shape. -/
def RawTerm.univNFRoot {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) : RawTerm scope :=
  if hIsIdCode : generator = .gen_idCode then
    match (hIsIdCode ▸ children : RawTermChildren (Generator.gen_idCode).binderShifts scope) with
    | .childCons child0 (.childCons child1 (.childCons child2 .childNil)) =>
        if child0.headIsUniverseCode then
          .mkGen .gen_equivCode () (.childCons child1 (.childCons child2 .childNil))
        else
          .mkGen generator payload children
  else
    .mkGen generator payload children

-- The bottom-up structural normalizer: normalize all children, then try the root rule.  Total structural
-- recursion — no `Acc`/SN.  (A `/-- -/` doc comment cannot precede `mutual`.)
mutual
  def RawTerm.univNF {scope : Nat} : RawTerm scope → RawTerm scope
    | .mkGen generator payload children =>
        RawTerm.univNFRoot generator payload (RawTermChildren.univNF children)
  def RawTermChildren.univNF {shifts : List Nat} {scope : Nat} :
      RawTermChildren shifts scope → RawTermChildren shifts scope
    | .childNil => .childNil
    | .childCons head tail => .childCons head.univNF tail.univNF
end

/-! ## Root-firing characterizations (the `fire` arm's computation) -/

/-- A `universeCode` node is a `univNF` fixpoint. -/
theorem univNF_universeCode {scope : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    (RawTerm.mkGen (scope := scope) .gen_universeCode (levelExpr, flag) .childNil).univNF
      = RawTerm.mkGen .gen_universeCode (levelExpr, flag) .childNil := rfl

/-- `univNFRoot` fires on an `idCode` with a `universeCode`-headed first child, yielding `equivCode` of the
other two children. -/
theorem univNFRoot_idCodeUniverse {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (child1 child2 : RawTerm scope) :
    RawTerm.univNFRoot .gen_idCode ()
      (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons child1 (.childCons child2 .childNil)))
    = RawTerm.mkGen .gen_equivCode () (.childCons child1 (.childCons child2 .childNil)) := rfl

/-- `univNFRoot` leaves an `equivCode` node untouched (its head is not `idCode`). -/
theorem univNFRoot_equivCode {scope : Nat} (child1 child2 : RawTerm scope) :
    RawTerm.univNFRoot .gen_equivCode ()
      (.childCons child1 (.childCons child2 .childNil))
    = RawTerm.mkGen .gen_equivCode () (.childCons child1 (.childCons child2 .childNil)) := rfl

/-! ## The preservation invariant — a single univalence step preserves the normal form -/

/-- **★ A single univalence step preserves the bottom-up normal form.**  `fire` reduces both sides to
`equivCode(A.univNF, B.univNF)`; congruence preserves `univNF` because `univNFRoot` is a function of the
normalized children, which the inductive hypothesis equates.  Explicit mutual recursor over an EQUALITY
motive (congruence by `congrArg`).  This invariant is confluence in computable form. -/
theorem univNF_preservesStep {scope : Nat} {source target : RawTerm scope}
    (step : UnivalenceRowStep source target) : source.univNF = target.univNF := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      UnivalenceRowStep first second → Prop :=
    fun {_} first second _ => first.univNF = second.univNF
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      UnivalenceRowStepChildren first second → Prop :=
    fun {_} {_} first second _ => first.univNF = second.univNF
  exact
    UnivalenceRowStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} levelExpr flag lhsCode rhsCode => by
        show (RawTerm.mkGen .gen_idCode ()
            (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
              (.childCons lhsCode (.childCons rhsCode .childNil)))).univNF
          = (RawTerm.mkGen .gen_equivCode ()
              (.childCons lhsCode (.childCons rhsCode .childNil))).univNF
        show RawTerm.univNFRoot .gen_idCode ()
            (.childCons (RawTerm.univNF (.mkGen .gen_universeCode (levelExpr, flag) .childNil))
              (.childCons lhsCode.univNF (.childCons rhsCode.univNF .childNil)))
          = RawTerm.univNFRoot .gen_equivCode ()
              (.childCons lhsCode.univNF (.childCons rhsCode.univNF .childNil))
        rw [univNF_universeCode, univNFRoot_idCodeUniverse, univNFRoot_equivCode])
      (fun {_} _gen _payload {children} {children'} _childStep childStepIH => by
        show RawTerm.univNFRoot _gen _payload (RawTermChildren.univNF children)
          = RawTerm.univNFRoot _gen _payload (RawTermChildren.univNF children')
        exact congrArg (RawTerm.univNFRoot _gen _payload) childStepIH)
      (fun {_} {_} {_} {head} {head'} rest _childStep childStepIH => by
        show RawTermChildren.childCons head.univNF (RawTermChildren.univNF rest)
          = RawTermChildren.childCons head'.univNF (RawTermChildren.univNF rest)
        exact congrArg (fun headNF => RawTermChildren.childCons headNF (RawTermChildren.univNF rest))
          childStepIH)
      (fun {_} {_} {_} head {rest} {rest'} _restStep restStepIH => by
        show RawTermChildren.childCons head.univNF (RawTermChildren.univNF rest)
          = RawTermChildren.childCons head.univNF (RawTermChildren.univNF rest')
        exact congrArg (fun restNF => RawTermChildren.childCons head.univNF restNF) restStepIH)
      step

end FX1Poly.Core

import FX1Poly.Core.Metatheory.Normalization.IotaSN.SizeCompatClosureSN
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepOverTable

/-! # FX1Poly/Core/Substrate/Univalence/DefinitionalUnivalenceRowSN
    — the FIRST instantiated strong-normalization theorem for a TABLE-NATIVE oriented row: the
    definitional-univalence row `Id_U A B ↝ Equiv A B` and its full congruence closure are strongly
    normalizing, by the structural `RawTerm.size` measure

`DefUnivSnResolution` pins (by `rfl`) that the univalence row is structurally recursive, substitution-free,
and `isRpoOrientable = true` — the CLASSIFIER verdict that the row OUGHT to be SN.  But it constructs no
`WellFounded`/`Acc`: the RPO route (`stepOverOrientedTable_wellFounded`) covers only the 14 RPO-orientable
LEGACY rows and excludes every table-native row by design (the RPO embedding has no bespoke arm for them,
and `iotaGenRank` puts `gen_idCode` and `gen_equivCode` at EQUAL rank 0, so the precedence clause yields no
root decrease).  So the univalence row's SN was argued-but-never-instantiated.

This file closes that gap.  The univalence rewrite DROPS the `universeCode` child
(`idCode(universeCode, A, B) ↝ equivCode(A, B)`), so it strictly decreases `RawTerm.size`; its compatible
(congruence) closure `UnivalenceRowStep` therefore reads SN off the generic size combinator
`wellFounded_of_sizeStrictlyDecreasing` — RPO-free, Tait-free, beta-free.  The root step is firing-linked to
the SHIPPED rule by `univalenceShapedDemoRule_firesOnUniverse`: `UnivalenceRowStep.fire`'s redex/reduct are
EXACTLY the spine on which the shipped `univalenceShapedDemoRule.firesOn?` produces its reduct — so this is
the SN of the real row's reduction, not a toy relation.

## What this ships

  * `UnivalenceRowStep` / `UnivalenceRowStepChildren` — the compatible (congruence) closure of the
    definitional-univalence root rewrite, mutual, mirroring `IotaStep`/`IotaStepChildren` (the root baked in
    rather than a higher-order parameter, which the positivity checker rejects).
  * **`UnivalenceRowStep.sizeStrictlyDecreases` (★)** — every step strictly decreases `RawTerm.size`; root
    by `RawTermChildren.size_lt_childCons_tail` (the reduct spine is the redex spine with the `universeCode`
    head dropped), congruence by the structural `RawSize` lemmas.  Explicit mutual recursor, core `Nat`
    arithmetic, no `omega`.
  * **`univalenceRowStep_wellFounded` (★)** — the univalence row's congruence closure is SN, via the
    generic size combinator.  The first instantiated WellFounded for a table-native row.
  * `univalenceRowStep_fireMatchesShippedRow` — the root step IS the shipped rule's firing (re-export of the
    shipped `firesOn?` characterization), so the closure is faithful, not a toy.
  * `univalenceRowStep_congSmoke` — the rule fires INSIDE a child (`cong ∘ here ∘ fire`), so the closure is
    inhabited at the congruence arm, not just the root.

## Honest scope

This is SN of the univalence row's congruence closure by `size` — the EASY half, because the row is
size-shrinking (a type-former-to-type-former drop).  It is NOT joint SN with beta/iota/eta: beta and the
Church-encoded iota successor cases GROW size, so the joint relation needs a Geser-style commuting-union of
the `size` and RPO measures (the open frontier).  And the bridge that would identify `UnivalenceRowStep`
verbatim with the shipped `StepOverTable [univalenceShapedDemoRule]` (the inductive soundness + the
`firesOn?` completeness inversion) is a bounded residual — the root step is firing-linked here, but the full
inductive equivalence is not yet shipped.  Markers below pin all three honestly.

## Zero-axiom verification

The mutual recursor `UnivalenceRowStep.rec` with a `Prop`-valued motive is propext-clean; size reductions
use `dsimp only` on the structural `RawSize` defs; the arithmetic is core `Nat.add_lt_add_right`/
`Nat.add_lt_add_left`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe (LevelExpr UniverseFlag)

-- The compatible (congruence) closure of the definitional-univalence root rewrite.  Root (`fire`) at the
-- head, or a step inside the children spine (`cong`, mutually with `UnivalenceRowStepChildren`).  Mirrors
-- `IotaStep`/`IotaStepChildren`; the root is BAKED IN (not a higher-order parameter, which the positivity
-- checker rejects).  (A `/-- -/` doc comment cannot precede `mutual`.)
mutual
  inductive UnivalenceRowStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
    | fire {scope : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag)
           (lhsCode rhsCode : RawTerm scope) :
        UnivalenceRowStep
          (.mkGen .gen_idCode ()
            (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
              (.childCons lhsCode (.childCons rhsCode .childNil))))
          (.mkGen .gen_equivCode ()
            (.childCons lhsCode (.childCons rhsCode .childNil)))
    | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
           {children children' : RawTermChildren gen.binderShifts scope}
           (childStep : UnivalenceRowStepChildren children children') :
        UnivalenceRowStep (.mkGen gen payload children) (.mkGen gen payload children')
  inductive UnivalenceRowStepChildren :
      {parentScope : Nat} → {binderShifts : List Nat} →
      RawTermChildren binderShifts parentScope →
      RawTermChildren binderShifts parentScope → Prop where
    | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
           {head head' : RawTerm (parentScope + headShift)}
           (rest : RawTermChildren restShifts parentScope)
           (childStep : UnivalenceRowStep head head') :
        UnivalenceRowStepChildren
          (RawTermChildren.childCons head rest) (RawTermChildren.childCons head' rest)
    | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
            (head : RawTerm (parentScope + headShift))
            {rest rest' : RawTermChildren restShifts parentScope}
            (restStep : UnivalenceRowStepChildren rest rest') :
        UnivalenceRowStepChildren
          (RawTermChildren.childCons head rest) (RawTermChildren.childCons head rest')
end

/-- **★ Every univalence-row congruence-closure step strictly decreases `RawTerm.size`.**  The root drops
the `universeCode` child, so the reduct spine is the redex spine's TAIL — strictly smaller by
`RawTermChildren.size_lt_childCons_tail`.  The `cong` node adds `+1` over the spine, and `here`/`there` add
the unchanged sibling sizes, so the strict child decrease lifts to the whole term.  Explicit mutual
recursor; core `Nat` arithmetic, no `omega`. -/
theorem UnivalenceRowStep.sizeStrictlyDecreases {scope : Nat} {source target : RawTerm scope}
    (step : UnivalenceRowStep source target) : target.size < source.size := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      UnivalenceRowStep first second → Prop :=
    fun {_} first second _ => second.size < first.size
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      UnivalenceRowStepChildren first second → Prop :=
    fun {_} {_} first second _ => second.size < first.size
  exact
    UnivalenceRowStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} _levelExpr _flag _lhsCode _rhsCode => by
        dsimp only [RawTerm.size]
        exact Nat.add_lt_add_right (RawTermChildren.size_lt_childCons_tail _ _) 1)
      (fun {_} _gen _payload {children} {children'} _childStep childStepIH => by
        dsimp only [RawTerm.size]
        exact Nat.add_lt_add_right childStepIH 1)
      (fun {_} {_} {_} {head} {head'} rest _childStep childStepIH => by
        dsimp only [RawTermChildren.size]
        exact Nat.add_lt_add_right (Nat.add_lt_add_right childStepIH rest.size) 1)
      (fun {_} {_} {_} head {rest} {rest'} _restStep restStepIH => by
        dsimp only [RawTermChildren.size]
        exact Nat.add_lt_add_right (Nat.add_lt_add_left restStepIH head.size) 1)
      step

/-- **★ The univalence row's congruence closure is strongly normalizing — by the structural `RawTerm.size`
measure, RPO-free and Tait-free.**  The first instantiated `WellFounded` for a table-native oriented row,
read off the generic size combinator `wellFounded_of_sizeStrictlyDecreasing`.  Closes the
`DefUnivSnResolution` gap (the row was classifier-pinned SN but never had an instantiated well-foundedness
object). -/
theorem univalenceRowStep_wellFounded {scope : Nat} :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      UnivalenceRowStep earlierTerm laterTerm) :=
  wellFounded_of_sizeStrictlyDecreasing UnivalenceRowStep.sizeStrictlyDecreases

/-- Every raw term is univalence-row strongly normalizing (accessible). -/
theorem UnivalenceRowStep.isStronglyNormalizing {scope : Nat} (sourceTerm : RawTerm scope) :
    Acc (fun (laterTerm earlierTerm : RawTerm scope) => UnivalenceRowStep earlierTerm laterTerm)
      sourceTerm :=
  univalenceRowStep_wellFounded.apply sourceTerm

/-- **The root step IS the shipped rule's firing.**  `UnivalenceRowStep.fire`'s redex applies `gen_idCode`
to the spine `universeCode ⟨lvl,flag⟩ , A , B`, and on EXACTLY that spine the shipped
`univalenceShapedDemoRule.firesOn?` produces `equivCode(A, B)` — `fire`'s reduct.  So the closure's root is
the real row firing, not an invented relation (re-export of the shipped `firesOn?` characterization). -/
theorem univalenceRowStep_fireMatchesShippedRow {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (lhsCode rhsCode : RawTerm scope) :
    univalenceShapedDemoRule.firesOn? ()
      (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons lhsCode (.childCons rhsCode .childNil)))
    = some (.mkGen .gen_equivCode ()
        (.childCons lhsCode (.childCons rhsCode .childNil))) :=
  univalenceShapedDemoRule_firesOnUniverse levelExpr flag lhsCode rhsCode

/-- **Non-vacuity at the congruence arm.**  The univalence rule fires INSIDE the function-position child of
`gen_app` (`cong ∘ here ∘ fire`), so the closure is inhabited beyond the root — the `cong`/`here` walk is
genuinely exercised. -/
theorem univalenceRowStep_congSmoke {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (lhsCode rhsCode sibling : RawTerm scope) :
    UnivalenceRowStep
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_idCode ()
            (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
              (.childCons lhsCode (.childCons rhsCode .childNil))))
          (.childCons sibling .childNil)))
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_equivCode ()
            (.childCons lhsCode (.childCons rhsCode .childNil)))
          (.childCons sibling .childNil))) :=
  UnivalenceRowStep.cong .gen_app ()
    (UnivalenceRowStepChildren.here _
      (UnivalenceRowStep.fire levelExpr flag lhsCode rhsCode))

/-- **Soundness (⊆): every univalence-row congruence-closure step IS a real shipped-table step.**
`UnivalenceRowStep` embeds into `StepOverTable [univalenceShapedDemoRule]` — root via `tableRedex` (the
singleton membership `List.Mem.head` + the shipped `firesOn?` firing), congruence via `StepOverTable.cong`,
mirroring `IotaStep.toStep`.  So the closure is a faithful SUB-relation of the shipped reduction over the
single-row table, not a toy.  (The converse ⊇ — which would transfer `univalenceRowStep_wellFounded` to the
shipped relation verbatim — needs the `firesOn?` completeness inversion; the bounded residual.) -/
theorem UnivalenceRowStep.toStepOverTable {scope : Nat} {source target : RawTerm scope}
    (step : UnivalenceRowStep source target) :
    StepOverTable [univalenceShapedDemoRule] source target := by
  let motiveStep : {scope : Nat} → (first second : RawTerm scope) →
      UnivalenceRowStep first second → Prop :=
    fun {_} first second _ => StepOverTable [univalenceShapedDemoRule] first second
  let motiveChildren : {parentScope : Nat} → {binderShifts : List Nat} →
      (first second : RawTermChildren binderShifts parentScope) →
      UnivalenceRowStepChildren first second → Prop :=
    fun {_} {_} first second _ => StepOverTableChildren [univalenceShapedDemoRule] first second
  exact
    UnivalenceRowStep.rec
      (motive_1 := motiveStep)
      (motive_2 := motiveChildren)
      (fun {_} levelExpr flag lhsCode rhsCode =>
        StepOverTable.tableRedex (rule := univalenceShapedDemoRule) (List.Mem.head _) ()
          (univalenceShapedDemoRule_firesOnUniverse levelExpr flag lhsCode rhsCode))
      (fun {_} gen payload {_} {_} _childStep childStepIH => StepOverTable.cong gen payload childStepIH)
      (fun {_} {_} {_} {_} {_} rest _childStep childStepIH => StepOverTableChildren.here rest childStepIH)
      (fun {_} {_} {_} head {_} {_} _restStep restStepIH => StepOverTableChildren.there head restStepIH)
      step

/-! ## Honest rails -/

/-- **Honesty marker.**  SN here is by the structural `RawTerm.size` measure, NOT the RPO — the univalence
row is size-shrinking but RPO-rank-equal (`gen_idCode` and `gen_equivCode` both at `iotaGenRank` 0), which
is exactly why the RPO route excludes it.  `= true`. -/
def fxUnivalenceRowSN_isSizeMeasureNotRpo : Bool := true

/-- **Honesty marker.**  This is NOT joint SN with beta/iota/eta — those can GROW `size` (beta duplication,
Church-encoded iota), so the joint relation needs a Geser-style commuting-union of the `size` and RPO
measures (the open frontier).  `= false`. -/
def fxUnivalenceRowSN_isJointWithBetaIota : Bool := false

/-- **Honesty marker.**  The closure's ROOT is firing-linked to the shipped rule
(`univalenceRowStep_fireMatchesShippedRow`), but the full inductive equivalence with
`StepOverTable [univalenceShapedDemoRule]` (soundness + the `firesOn?` completeness inversion) is a bounded
residual, not yet shipped.  `= false`. -/
def fxUnivalenceRowSN_coversShippedTableRelationVerbatim : Bool := false

end FX1Poly.Core

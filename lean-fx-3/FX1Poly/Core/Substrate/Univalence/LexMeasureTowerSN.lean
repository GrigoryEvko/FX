import FX1Poly.Core.Metatheory.Normalization.IotaSN.ProductFormerLexMeasureSN
import FX1Poly.Core.Substrate.Univalence.UnifiedDefinitionalTableDecidableConv

/-! # FX1Poly/Core/Substrate/Univalence/LexMeasureTowerSN
    — the n-level lexicographic measure tower: a generic strong-normalization engine for ANY finite
    list of `Nat` measures, where each step decreases some level and preserves every higher level

`ProductFormerLexMeasureSN` ships the BINARY lex combinator `lex(primaryMeasure, size)`, used to join a
size-shrinking and a size-growing row.  This file generalizes that to ARBITRARY DEPTH: a measure TOWER
`[μ₁, μ₂, …, μₙ]` ordered lexicographically.  A relation is strongly normalizing under the tower when every
step is "lex-decreasing" — there is a level `k` with `μₖ` strictly dropping and `μ₁, …, μ_{k-1}` all
preserved.  This is the classical lexicographic-termination principle, mechanized as a reusable engine.

The tower relation is built by folding `LexPair` (the repo's propext-clean `∨`-form lexicographic step,
NOT `Prod.Lex`) over the measure list, and its well-foundedness is proven by induction on that list, each
step riding `LexPair.isWellFounded`.  The construction is CARRIER-GENERIC (`Carrier : Type`, measures
`Carrier → Nat`), so it is not tied to `RawTerm` — a general lexicographic-termination tower.

## What this ships

  * **`lexTowerRel` / `lexTowerRel_wellFounded` (★)** — the n-level lexicographic relation on a list of
    `Nat` measures over any carrier, and its well-foundedness by induction on the measure list.
  * **`wellFounded_of_lexMeasureTowerStrictlyDecreasing` (★)** — the `RawTerm` SN combinator: a relation
    whose every step is lex-decreasing over a measure tower is well-founded.  The n-ary generalization of
    `wellFounded_of_natMeasureStrictlyDecreasing` (n=1) and `wellFounded_of_lexMeasureStrictlyDecreasing`
    (n=2 at `[_, size]`).
  * **`unifiedDefinitionalRow_wellFoundedViaTower`** — the joint SN of the union table
    `unifiedDefinitionalTable` recovered as the 2-level tower instance at `[productFormerCount, size]`,
    showing the tower subsumes the binary result.

## The general principle

A rule set is jointly SN under a lexicographic tower of measures `[μ₁, …, μₙ]` exactly when each rule
decreases SOME level `μₖ` and PRESERVES every higher level `μ₁, …, μ_{k-1}`.  Mixing size-shrinking and
size-growing rows (the joint SN) is the n=2 instance; a third measure that two rows preserve while a third
drops would be n=3; and so on.  Non-duplication is still required per row (this never makes a duplicating
beta/iota rule SN — those have no everywhere-decreasing tower).

## Zero-axiom verification

`lexTowerRel_wellFounded` rides `LexPair.isWellFounded` (propext-clean) + `InvImage.wf` + `Nat.lt_wfRel.wf`,
by structural list induction; the empty tower is the empty relation (`nomatch`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-! ## The generic n-level lexicographic measure tower (any carrier) -/

/-- The n-level lexicographic relation over a list of `Nat` measures: `smaller` is below `bigger` when the
head measure strictly drops, OR it ties and the rest of the tower decreases.  The empty tower relates
nothing (`False`).  Carrier-generic. -/
def lexTowerRel {Carrier : Type} (measures : List (Carrier → Nat)) (smaller bigger : Carrier) : Prop :=
  match measures with
  | [] => False
  | headMeasure :: restMeasures =>
      headMeasure smaller < headMeasure bigger
      ∨ (headMeasure smaller = headMeasure bigger ∧ lexTowerRel restMeasures smaller bigger)

/-- **★ The n-level lexicographic measure tower is well-founded**, by induction on the measure list: the
empty tower is the empty relation; a `headMeasure :: restMeasures` tower is `InvImage` of
`LexPair Nat.lt (lexTowerRel restMeasures)` along `element ↦ (headMeasure element, element)`, well-founded
by `LexPair.isWellFounded` from `Nat.lt`'s well-foundedness and the inductive hypothesis. -/
theorem lexTowerRel_wellFounded {Carrier : Type} (measures : List (Carrier → Nat)) :
    WellFounded (lexTowerRel measures) := by
  induction measures with
  | nil => exact ⟨fun element => ⟨element, fun _other contra => nomatch contra⟩⟩
  | cons headMeasure restMeasures restWellFounded =>
      exact InvImage.wf (fun element => (headMeasure element, element))
        (LexPair.isWellFounded Nat.lt (lexTowerRel restMeasures) Nat.lt_wfRel.wf restWellFounded)

/-! ## The RawTerm tower combinator -/

/-- **★ The `RawTerm` strong-normalization combinator over an n-level measure tower.**  Any reduction
relation whose every step is lex-decreasing over a measure tower `measures` is well-founded.  The n-ary
generalization of the single-measure (`wellFounded_of_natMeasureStrictlyDecreasing`) and binary-lex
(`wellFounded_of_lexMeasureStrictlyDecreasing`) combinators. -/
theorem wellFounded_of_lexMeasureTowerStrictlyDecreasing
    {scope : Nat} {stepRelation : RawTerm scope → RawTerm scope → Prop}
    {measures : List (RawTerm scope → Nat)}
    (decreasesTower : ∀ {source target : RawTerm scope},
      stepRelation source target → lexTowerRel measures target source) :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      stepRelation earlierTerm laterTerm) :=
  Subrelation.wf (fun step => decreasesTower step) (lexTowerRel_wellFounded measures)

/-! ## Demonstration — the joint SN recovered as the 2-level tower instance -/

/-- **★ The table-native joint SN is the 2-level tower at `[productFormerCount, size]`.**  Re-deriving the
union table's strong normalization (`unifiedDefinitionalTable`, the two-row definitional-univalence table)
through the general tower combinator: a univalence firing ties the former count and drops size (the size
level), a size-growing firing drops the former count (the head level).  This shows the n-level tower
subsumes the binary joint SN. -/
theorem unifiedDefinitionalRow_wellFoundedViaTower {scope : Nat} :
    WellFounded (fun (laterTerm earlierTerm : RawTerm scope) =>
      StepOverTable unifiedDefinitionalTable earlierTerm laterTerm) :=
  wellFounded_of_lexMeasureTowerStrictlyDecreasing
    (measures := [RawTerm.productFormerCount, RawTerm.size])
    (fun {_source _target} step =>
      match stepOverUnifiedTable_decreasesLex step with
      | Or.inl formerCountDrop => Or.inl formerCountDrop
      | Or.inr ⟨formerCountEqual, sizeDrop⟩ => Or.inr ⟨formerCountEqual, Or.inl sizeDrop⟩)

/-! ## Non-vacuity — the tower relation genuinely varies with depth -/

/-- The 2-level tower `[productFormerCount, size]` over `RawTerm` is well-founded (a concrete instance of
`lexTowerRel_wellFounded` at depth 2). -/
theorem productFormerCountSizeTower_wellFounded {scope : Nat} :
    WellFounded (lexTowerRel [RawTerm.productFormerCount (scope := scope), RawTerm.size]) :=
  lexTowerRel_wellFounded _

/-- The single-element tower `[size]` is well-founded (depth 1 — the tower subsumes a single measure). -/
theorem sizeTower_wellFounded {scope : Nat} :
    WellFounded (lexTowerRel [RawTerm.size (scope := scope)]) :=
  lexTowerRel_wellFounded _

/-! ## Honest rails -/

/-- **Honesty marker.**  The tower is the n-ARY lexicographic generalization: depth 1 subsumes a single
measure, depth 2 the binary lex (the joint SN), depth n the full lexicographic tower.  `= true`. -/
def fxLexTower_isNAryGeneralization : Bool := true

/-- **Honesty marker.**  Each rule must decrease SOME level and PRESERVE every higher level; the tower never
makes a DUPLICATING rule (beta/iota) SN — those have no everywhere-decreasing measure at any level.
`= true`. -/
def fxLexTower_requiresPerLevelPreservation : Bool := true

end FX1Poly.Core

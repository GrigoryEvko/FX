import FX1Poly.Tier0.Term.Generator.GeneratorCore
import FX1Poly.Tier0.Type.Level.LevelExpr
import FX1Poly.Tier0.Type.Universe.UniverseFlag

/-! # FX1Poly/Typed/Engine/RuleTables/CellTemplate
    — the closed CellTemplate DSL for typing-rule outputs + classifiers (SR-DSL-0a, the data)

The typing-side twin of the shipped reduct DSL `ReductTemplate` (IotaRuleTable.lean): every typing rule's OUTPUT
TYPE and every OBLIGATION CLASSIFIER becomes a structured `CellTemplate` value, so that subject-reduction's drift
+ type-SR become ONE induction on the DSL instead of per-eliminator arms.  This file is SR-DSL-0a — the DATA only
(the inductives + the structural well-formedness `Bool`); `interpret?` is SR-DSL-0b, the faithfulness bridges are
SR-DSL-0c, and `isFlagCoherent` lands with the rule-descriptor refactor (SR-DSL-3, where the rule's flag-witness
obligation context is available).

## The design (locked, see the SR-DSL design-lock memory)

Modeled on `ReductTemplate`'s closed-inductive discipline (invariant I1 — NEVER an opaque `RawTerm`-valued
function, so drift is unconditional via `Conv.ofChildren`).  Differences from `ReductTemplate`, all driven by the
TYPING side:

  * two child vectors at interpretation — the cell's own children (`args`) and the derivation-chosen type-index
    `params` — addressed by `ChildRef`;
  * a `universeCode` leaf carrying a `LevelSource` / `FlagSource` (the universe existentials `level0`/`level1`/
    `carrierLevel`/`levels`/`flag` that formation outputs + every universe-code formedness classifier read, and
    which live in NEITHER `args` nor `params`);
  * the five multi-binder dependent-branch re-basings as `macroReBasing` leaves that interpret to the shipped
    `…DependentSuccBranchType` / `…SomeBranchCodomain` / `…ConsBranchType` defs (their subst/rename naturality is
    the existing per-macro `…_iterateLift` lemmas — so the DSL's denote-commutes-with-subst is one induction
    dispatching to those leaves).

Every constructor is FORCED by a census shape across `ElimRuleTable`/`IntroRuleTable`/`FormationRuleTable` (16
output shapes, 19 classifier shapes); no gratuitous constructor.  `builtGen` is SIMPLER than `ReductTemplate`'s:
all current type-formers + data type cells carry a `()` payload, and the only non-`Unit` payload (the universe
code's level/flag pair) is the dedicated `universeCode` leaf — so `builtGen` needs no `PayloadSource`.

## Zero-axiom verification

Pure data inductives + a structural `Bool` fold over `Nat.blt` (no `propext`/`Quot.sound`/`Classical`/`omega`).
No `deriving` (kept off to avoid match-compiler axiom leaks; `CellTemplate.beq` for I5 is shipped with SR-DSL-6
where it is consumed).  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A reference to one of the typing cell's own children (the rule's `args`) or to a derivation-chosen
type-index `param`.  Positional, never by name — the args/params split mirrors the `ElimRule`/`IntroRule`
`argShifts`/`paramShifts` descriptor fields. -/
inductive ChildRef where
  /-- The `args` child at this slot (the cell's own children). -/
  | argChild (slot : Nat)
  /-- The `params` (type-index) child at this slot. -/
  | paramChild (slot : Nat)

/-- Where a `universeCode` leaf's LEVEL comes from — the rule's level existentials, the `levels` telescope
(positional slot or `lmaxAll`), or a pinned literal (the base/nullary formation rows pin `lzero`). -/
inductive LevelSource where
  /-- The elim/intro arm's first universe existential `level0`. -/
  | level0Existential
  /-- The elim/intro arm's second universe existential `level1`. -/
  | level1Existential
  /-- The term-indexed former's carrier `level` existential. -/
  | carrierLevelExistential
  /-- `lmaxAll levels` — the flat/cumulative formation output. -/
  | levelMaxAll
  /-- `levels[index]` (with a forced-`lzero` fallback) — the positional zip of children with the level list. -/
  | levelSlot (index : Nat)
  /-- A pinned literal level (the base/nullary formation output ignores the rule's level, pinning `lzero`). -/
  | literalLevel (value : LevelExpr)

/-- Where a `universeCode` leaf's FLAG comes from — the rule's threaded `flag`, or a pinned literal (the
base/nullary formation output pins `standard`). -/
inductive FlagSource where
  /-- The rule's single threaded `flag` existential. -/
  | ruleFlag
  /-- A pinned literal flag. -/
  | literalFlag (value : UniverseFlag)

/-- The multi-binder dependent-branch re-basings — each interprets to the shipped bespoke `def` over the motive
child (their subst/rename naturality is the existing per-macro `…_iterateLift` lemma).  No compositional node
above reproduces these simultaneous binder-injecting re-basings, so they are forced macro leaves. -/
inductive ReBasingMacro where
  /-- `natElimDependentSuccBranchType motive` — the two-binder `subst (cons (natSucc (var 1)) shift2) motive`
      (natElim/natRec step branch, at `scope + 2`). -/
  | natSuccBranchType
  /-- `…DependentSomeBranchCodomain` / `…InlBranchCodomain` / `…InrBranchCodomain` — the one-binder
      `subst (cons (INJECTION (var 0)) shift1) motive` (option-some / either-inl / either-inr branch codomain),
      parameterised by the injection constructor head. -/
  | injectionBranchCodomain (injectionHead : Generator)
  /-- `listElimDependentConsBranchType motive elementType` — the three-nested-`piTyCode` cons branch type with
      two motive re-basings (absorbs the weakened-element-type into one macro, closing expressiveness gap G1). -/
  | listConsBranchType

mutual

/-- A structured template for a typing-rule output type or obligation classifier.  `interpret?` (SR-DSL-0b)
turns it into a `RawTerm` given the children (`args` + `params`) and the universe existentials, depth-graded.
Every constructor is forced by the output/classifier census (srdsl_expressiveness.md §1). -/
inductive CellTemplate where
  /-- A child (arg or param) at binder shift 0, weakened to the current depth.  The projection leaf. -/
  | childAt (childReference : ChildRef)
  /-- A template-introduced binder (innermost = 0; valid only under enough `builtGen`/macro binders). -/
  | boundVarAt (binderIndex : Nat)
  /-- A literal closed nullary cell `mkGen nullaryHead () .childNil`, weakened — the closed value/type codes
      (`natZero`, `boolTrue`/`boolFalse`, `optionNone`, `listNil`, the interval endpoints, and the closed type
      codes nat/bool/unit/interval). -/
  | literalCell (nullaryHead : Generator)
  /-- `universeCodeCell <level> <flag>` with the level/flag chosen from the universe existentials, weakened —
      the universe-code outputs (FO1-FO3) and every universe-code formedness classifier (C5/C6/C17). -/
  | universeCode (levelSource : LevelSource) (flagSource : FlagSource)
  /-- Build a cell of any generator with a `()` payload and template children (each at the head's own binder
      shift) — the type-formers `piTyCodeCell` + the data type cells (option/either/product/list/id/bridge). -/
  | builtGen (head : Generator) (childTemplates : CellTemplateSpine)
  /-- `subst0 (body) (argument)` where `body` is the one-binder child at `bodyReference` (shift 1) and
      `argument` is the interpreted sub-template — the app output, every dependent-eliminator output, and the
      base/nullary-branch classifiers (`subst0 motive natZeroCell`, etc.). -/
  | subst0Into (bodyReference : ChildRef) (argumentTemplate : CellTemplate)
  /-- `substPair (body) (inner) (outer)` where `body` is the two-binder child at `bodyReference` (shift 2) — the
      `idJMotiveAt` output and the idJ base-case classifier. -/
  | substPairInto (bodyReference : ChildRef) (innerTemplate outerTemplate : CellTemplate)
  /-- A multi-binder dependent-branch re-basing over the motive child at `motiveReference` — interprets to the
      shipped bespoke `def` (the only place a non-compositional constructor is justified). -/
  | macroReBasing (reBasingMacro : ReBasingMacro) (motiveReference : ChildRef)

/-- The child templates of a `builtGen` node — a hand-rolled list (mutual sibling, not a nested `List`) to keep
the recursion plainly structural and propext-clean, exactly as `ReductTemplateSpine`. -/
inductive CellTemplateSpine where
  | spineNil
  | spineCons (headTemplate : CellTemplate) (restTemplates : CellTemplateSpine)

end

/-- A `ChildRef` addresses an in-range child for the given arg/param arities. -/
def ChildRef.isInRange (argArity paramArity : Nat) : ChildRef → Bool
  | .argChild slot => Nat.blt slot argArity
  | .paramChild slot => Nat.blt slot paramArity

mutual

/-- **The structural well-formedness `Bool`** — the template references only in-range children.  The decidable
(`rfl`-checkable) sanity fold the `WfBundleSR` certificate runs over each row (invariant I2 — Bool, never Prop).
A malformed row (slot out of range) makes the certificate's `rfl` fail, naming exactly the rejecting row. -/
def CellTemplate.isWellFormed (argArity paramArity : Nat) : CellTemplate → Bool
  | .childAt childReference => childReference.isInRange argArity paramArity
  | .boundVarAt _ => true
  | .literalCell _ => true
  | .universeCode _ _ => true
  | .builtGen _ childTemplates => childTemplates.allWellFormed argArity paramArity
  | .subst0Into bodyReference argumentTemplate =>
      bodyReference.isInRange argArity paramArity && argumentTemplate.isWellFormed argArity paramArity
  | .substPairInto bodyReference innerTemplate outerTemplate =>
      bodyReference.isInRange argArity paramArity
        && innerTemplate.isWellFormed argArity paramArity
        && outerTemplate.isWellFormed argArity paramArity
  | .macroReBasing _ motiveReference => motiveReference.isInRange argArity paramArity

/-- Every child template in a `builtGen` spine is well-formed for the given arities. -/
def CellTemplateSpine.allWellFormed (argArity paramArity : Nat) : CellTemplateSpine → Bool
  | .spineNil => true
  | .spineCons headTemplate restTemplates =>
      headTemplate.isWellFormed argArity paramArity && restTemplates.allWellFormed argArity paramArity

end

end FX1Poly.Typed

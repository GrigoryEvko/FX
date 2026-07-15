import FX1Poly.Axis.Term.Generator.GeneratorCore
import FX1Poly.Axis.Type.Level.LevelExpr
import FX1Poly.Axis.Type.Universe.UniverseFlag
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDesc
import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.ListElimDependentConsType

/-! # FX1Poly/Typed/Engine/RuleTables/CellTemplate
    — the closed CellTemplate DSL + interpreter for typing-rule outputs + classifiers (SR-DSL-0a data + 0b interpret?)

The typing-side twin of the shipped reduct DSL `ReductTemplate` (IotaRuleTable.lean): every typing rule's OUTPUT
TYPE and every OBLIGATION CLASSIFIER becomes a structured `CellTemplate` value, so that subject-reduction's drift
+ type-SR become ONE induction on the DSL instead of per-eliminator arms.  This file holds SR-DSL-0a — the DATA
(the inductives + the structural well-formedness `Bool`) — AND SR-DSL-0b — the `CellTemplate.interpret?`
depth-graded interpreter (the section at the bottom, mirroring `IotaRuleDesc.interpretTemplate?`).  The
faithfulness bridges (`interpret? = the shipped outputType/classifier`, `rfl`-per-row) are SR-DSL-0c, and
`isFlagCoherent` lands with the rule-descriptor refactor (SR-DSL-3, where the rule's flag-witness obligation
context is available).

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

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

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
      (natElim/natRec step branch, at `scope + 2`).  The motive is the child at `motiveReference` (shift 1). -/
  | natSuccBranchType (motiveReference : ChildRef)
  /-- `…DependentSomeBranchCodomain` / `…InlBranchCodomain` / `…InrBranchCodomain` — the one-binder
      `subst (cons (INJECTION (var 0)) shift1) motive` (option-some / either-inl / either-inr branch codomain),
      parameterised by the injection constructor head; the motive is at `motiveReference` (shift 1). -/
  | injectionBranchCodomain (injectionHead : Generator) (motiveReference : ChildRef)
  /-- `listElimDependentConsBranchType motive elementType` — the three-nested-`piTyCode` cons branch type with
      two motive re-basings (absorbs the weakened-element-type into one macro, closing expressiveness gap G1).
      Takes the motive at `motiveReference` (shift 1) and the element type at `elementTypeReference` (a param). -/
  | listConsBranchType (motiveReference : ChildRef) (elementTypeReference : ChildRef)

mutual

/-- A structured template for a typing-rule output type or obligation classifier.  `interpret?` (SR-DSL-0b)
turns it into a `RawTerm` given the children (`args` + `params`) and the universe existentials, depth-graded.
Every constructor is forced by the output/classifier census (srdsl_expressiveness.md §1). -/
inductive CellTemplate where
  /-- A child (arg or param) at binder shift 0, weakened to the current depth.  The projection leaf. -/
  | childAt (childReference : ChildRef)
  /-- A child (arg or param) that is a ONE-BINDER BODY (binder shift 1), placed raw (keeping its own binder
      innermost) and weakened to the current depth.  The single shipped use is `app`'s `codomainCode` type-index
      param (a shift-1 body) placed raw as the `piTyCodeCell` codomain child — the one raw shift-1 placement the
      shift-0 `childAt` cannot reach.  Interprets only at depth `>= 1` (a one-binder body cannot sit at depth 0). -/
  | childBodyAt (childReference : ChildRef)
  /-- A template-introduced binder (innermost = 0; valid only under enough `builtGen`/macro binders). -/
  | boundVarAt (binderIndex : Nat)
  /-- `universeCodeCell <level> <flag>` with the level/flag chosen from the universe existentials, weakened —
      the universe-code outputs (FO1-FO3) and every universe-code formedness classifier (C5/C6/C17).  The
      universe code is its OWN leaf (not a `builtGen`) because its payload is the `(level, flag)` pair, not `()`. -/
  | universeCode (levelSource : LevelSource) (flagSource : FlagSource)
  /-- Build a cell of `head` from a scope-uniform `payloadFamily` (`fun _ => ()` for every type-former, data-type
      cell, and nullary value/type code — the only payloads the typing side builds; the `constantFamily` of
      `ReductTemplate`'s `PayloadSource`) and template children evaluated at the head's OWN binder shifts.
      Subsumes the type-formers (`piTyCodeCell`), the data type cells (option/either/product/list/id/bridge), AND
      the closed nullary value/type codes (`natZeroCell`/`boolTrueCell`/… via an empty `childTemplates`) — so no
      separate `literalCell`.  Carrying `payloadFamily` (rather than assuming `()`) is what lets `interpret?`
      build `mkGen head payload children` for a VARIABLE `head` whose `payload` type is otherwise opaque. -/
  | builtGen (head : Generator) (payloadFamily : (anyScope : Nat) → head.payload anyScope)
      (childTemplates : CellTemplateSpine)
  /-- `subst0 (body) (argument)` where `body` is the one-binder child at `bodyReference` (shift 1) and
      `argument` is the interpreted sub-template — the app output, every dependent-eliminator output, and the
      base/nullary-branch classifiers (`subst0 motive natZeroCell`, etc.). -/
  | subst0Into (bodyReference : ChildRef) (argumentTemplate : CellTemplate)
  /-- `substPair (body) (inner) (outer)` where `body` is the two-binder child at `bodyReference` (shift 2) — the
      `idJMotiveAt` output and the idJ base-case classifier. -/
  | substPairInto (bodyReference : ChildRef) (innerTemplate outerTemplate : CellTemplate)
  /-- A multi-binder dependent-branch re-basing — interprets to the shipped bespoke `def` over the child refs the
      macro carries (the only place a non-compositional constructor is justified). -/
  | macroReBasing (reBasingMacro : ReBasingMacro)

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

/-- Every child reference a re-basing macro carries is in range. -/
def ReBasingMacro.refsInRange (argArity paramArity : Nat) : ReBasingMacro → Bool
  | .natSuccBranchType motiveReference => motiveReference.isInRange argArity paramArity
  | .injectionBranchCodomain _ motiveReference => motiveReference.isInRange argArity paramArity
  | .listConsBranchType motiveReference elementTypeReference =>
      motiveReference.isInRange argArity paramArity && elementTypeReference.isInRange argArity paramArity

mutual

/-- **The structural well-formedness `Bool`** — the template references only in-range children.  The decidable
(`rfl`-checkable) sanity fold the `WfBundleSR` certificate runs over each row (invariant I2 — Bool, never Prop).
A malformed row (slot out of range) makes the certificate's `rfl` fail, naming exactly the rejecting row. -/
def CellTemplate.isWellFormed (argArity paramArity : Nat) : CellTemplate → Bool
  | .childAt childReference => childReference.isInRange argArity paramArity
  | .childBodyAt childReference => childReference.isInRange argArity paramArity
  | .boundVarAt _ => true
  | .universeCode _ _ => true
  | .builtGen _ _ childTemplates => childTemplates.allWellFormed argArity paramArity
  | .subst0Into bodyReference argumentTemplate =>
      bodyReference.isInRange argArity paramArity && argumentTemplate.isWellFormed argArity paramArity
  | .substPairInto bodyReference innerTemplate outerTemplate =>
      bodyReference.isInRange argArity paramArity
        && innerTemplate.isWellFormed argArity paramArity
        && outerTemplate.isWellFormed argArity paramArity
  | .macroReBasing reBasingMacro => reBasingMacro.refsInRange argArity paramArity

/-- Every child template in a `builtGen` spine is well-formed for the given arities. -/
def CellTemplateSpine.allWellFormed (argArity paramArity : Nat) : CellTemplateSpine → Bool
  | .spineNil => true
  | .spineCons headTemplate restTemplates =>
      headTemplate.isWellFormed argArity paramArity && restTemplates.allWellFormed argArity paramArity

end

/-! ## The template interpreter (SR-DSL-0b) — the typing-side twin of `IotaRuleDesc.interpretTemplate?`

`interpret?` turns a `CellTemplate` into a `RawTerm` given the eliminator cell's children (`args`), the
derivation-chosen type-index children (`params`), and the universe existentials (`levels` / `level0` / `level1` /
`carrierLevel` / `flag`), graded by a binder DEPTH.  It mirrors `IotaRuleDesc.interpretTemplate?`
(IotaRuleTable.lean) arm-for-arm — Option-valued, depth-graded, shift-checked via the SHARED `ScopedChild`
machinery (`scopedChildAt?` + `atShift{Zero,One,Two}?`) and the SHARED depth weakenings (`weakenBy depth` /
`weakenBodyUnder{One,Two}BinderBy`) — with the typing-side additions: the TWO child vectors (`args` + `params`)
addressed by `ChildRef`; the `universeCode` leaf reading the level/flag existentials; and the `macroReBasing`
leaves dispatching to the shipped dependent-branch defs via the DEPTH-PEEL (a macro of intrinsic `+k` matches
`depth` as `innerDepth + k`, so `weakenBody…By innerDepth (shippedDef …)` lands at `RawTerm (scope+depth)` and at
the exact call depth `k` reduces to the shipped def itself — the `rfl` SR-DSL-0c target).  Total on the rows;
`none` on shape mismatch. -/

/-- Resolve a `ChildRef` to a shift-tagged child of the addressed vector (`args` for `argChild`, `params` for
`paramChild`). -/
def resolveChildRef? {argShifts paramShifts : List Nat} {scope : Nat}
    (args : RawTermChildren argShifts scope) (params : RawTermChildren paramShifts scope) :
    ChildRef → Option (ScopedChild scope)
  | .argChild slot => scopedChildAt? args.toScopedChildren slot
  | .paramChild slot => scopedChildAt? params.toScopedChildren slot

/-- Resolve a `LevelSource` against the rule's universe existentials. -/
def resolveLevelSource (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) :
    LevelSource → LevelExpr
  | .level0Existential => level0
  | .level1Existential => level1
  | .carrierLevelExistential => carrierLevel
  | .levelMaxAll => lmaxAll levels
  | .levelSlot index => (listEntryAt? levels index).getD .lzero
  | .literalLevel value => value

/-- Resolve a `FlagSource` against the rule's threaded flag. -/
def resolveFlagSource (flag : UniverseFlag) : FlagSource → UniverseFlag
  | .ruleFlag => flag
  | .literalFlag value => value

mutual

/-- Interpret a `CellTemplate` against the cell's children + type-index params + universe existentials at a
binder depth (the typing-side twin of `IotaRuleDesc.interpretTemplate?`; see the section docstring). -/
def CellTemplate.interpret? {argShifts paramShifts : List Nat} {scope : Nat}
    (args : RawTermChildren argShifts scope) (params : RawTermChildren paramShifts scope)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    (depth : Nat) → CellTemplate → Option (RawTerm (scope + depth))
  | depth, .childAt childReference => do
      let child ← resolveChildRef? args params childReference
      let childTerm ← child.atShiftZero?
      some (RawTerm.weakenBy depth childTerm)
  | depth, .childBodyAt childReference =>
      match depth with
      | 0 => none
      | innerDepth + 1 => do
          let child ← resolveChildRef? args params childReference
          let childBody ← child.atShiftOne?
          some (RawTerm.weakenBodyUnderOneBinderBy innerDepth childBody)
  | depth, .boundVarAt binderIndex =>
      if isTemplateBound : binderIndex < depth then
        some (.mkGen .gen_var
          ⟨binderIndex, Nat.lt_of_lt_of_le isTemplateBound (Nat.le_add_left depth scope)⟩ .childNil)
      else none
  | depth, .universeCode levelSource flagSource =>
      some (RawTerm.weakenBy depth
        (universeCodeCell (resolveLevelSource levels level0 level1 carrierLevel levelSource)
          (resolveFlagSource flag flagSource)))
  | depth, .builtGen head payloadFamily childTemplates => do
      let builtChildren ← interpretSpine? args params levels level0 level1 carrierLevel flag
        depth head.binderShifts childTemplates
      some (.mkGen head (payloadFamily (scope + depth)) builtChildren)
  | depth, .subst0Into bodyReference argumentTemplate => do
      let argTerm ←
        CellTemplate.interpret? args params levels level0 level1 carrierLevel flag depth argumentTemplate
      let bodyChild ← resolveChildRef? args params bodyReference
      let bodyTerm ← bodyChild.atShiftOne?
      some (RawTerm.subst0 (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm) argTerm)
  | depth, .substPairInto bodyReference innerTemplate outerTemplate => do
      let innerTerm ←
        CellTemplate.interpret? args params levels level0 level1 carrierLevel flag depth innerTemplate
      let outerTerm ←
        CellTemplate.interpret? args params levels level0 level1 carrierLevel flag depth outerTemplate
      let bodyChild ← resolveChildRef? args params bodyReference
      let bodyTerm ← bodyChild.atShiftTwo?
      some (RawTerm.substPair (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm) innerTerm outerTerm)
  | depth, .macroReBasing reBasingMacro =>
      match reBasingMacro with
      | .natSuccBranchType motiveReference =>
          match depth with
          | 0 => none
          | 1 => none
          | innerDepth + 2 => do
              let motiveChild ← resolveChildRef? args params motiveReference
              let motiveBody ← motiveChild.atShiftOne?
              some (RawTerm.weakenBodyUnderTwoBindersBy innerDepth
                (natElimDependentSuccBranchType motiveBody))
      | .injectionBranchCodomain injectionHead motiveReference =>
          match depth with
          | 0 => none
          | innerDepth + 1 => do
              let motiveChild ← resolveChildRef? args params motiveReference
              let motiveBody ← motiveChild.atShiftOne?
              let codomain ←
                if injectionHead = .gen_optionSome then
                  some (optionMatchDependentSomeBranchCodomain motiveBody)
                else if injectionHead = .gen_eitherInl then
                  some (eitherMatchDependentInlBranchCodomain motiveBody)
                else if injectionHead = .gen_eitherInr then
                  some (eitherMatchDependentInrBranchCodomain motiveBody)
                else none
              some (RawTerm.weakenBodyUnderOneBinderBy innerDepth codomain)
      | .listConsBranchType motiveReference elementTypeReference => do
          let motiveChild ← resolveChildRef? args params motiveReference
          let motiveBody ← motiveChild.atShiftOne?
          let elementChild ← resolveChildRef? args params elementTypeReference
          let elementType ← elementChild.atShiftZero?
          some (RawTerm.weakenBy depth (listElimDependentConsBranchType motiveBody elementType))

/-- Interpret a `builtGen` node's child templates, each at the built generator's OWN binder shift on top of the
current depth (shift-0 at `depth`, shift-1 at `depth+1`, shift-2 at `depth+2`).  Mirrors
`IotaRuleDesc.interpretBuiltChildren?`. -/
def interpretSpine? {argShifts paramShifts : List Nat} {scope : Nat}
    (args : RawTermChildren argShifts scope) (params : RawTermChildren paramShifts scope)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) (depth : Nat) :
    (childShifts : List Nat) → CellTemplateSpine → Option (RawTermChildren childShifts (scope + depth))
  | [], .spineNil => some .childNil
  | [], .spineCons _ _ => none
  | _ :: _, .spineNil => none
  | 0 :: restShifts, .spineCons headTemplate restTemplates => do
      let childTerm ←
        CellTemplate.interpret? args params levels level0 level1 carrierLevel flag depth headTemplate
      let restChildren ←
        interpretSpine? args params levels level0 level1 carrierLevel flag depth restShifts restTemplates
      some (.childCons childTerm restChildren)
  | 1 :: restShifts, .spineCons headTemplate restTemplates => do
      let childTerm ←
        CellTemplate.interpret? args params levels level0 level1 carrierLevel flag (depth + 1) headTemplate
      let restChildren ←
        interpretSpine? args params levels level0 level1 carrierLevel flag depth restShifts restTemplates
      some (.childCons childTerm restChildren)
  | 2 :: restShifts, .spineCons headTemplate restTemplates => do
      let childTerm ←
        CellTemplate.interpret? args params levels level0 level1 carrierLevel flag (depth + 2) headTemplate
      let restChildren ←
        interpretSpine? args params levels level0 level1 carrierLevel flag depth restShifts restTemplates
      some (.childCons childTerm restChildren)
  | (_ + 3) :: _, .spineCons _ _ => none

end

end FX1Poly.Typed

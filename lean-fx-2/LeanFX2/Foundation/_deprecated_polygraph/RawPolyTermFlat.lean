import LeanFX2.Foundation._deprecated_polygraph.Generator

/-! # `RawPolyTermFlat` — honest nested polygraph substrate (P2.3).

This file ships the **honest nested inductive** counterpart to the
legacy 74-ctor mirror `RawPolyTerm` (K11.8 / #1756): a substrate
where ONE `mk` constructor carries a `Generator` tag, a per-generator
payload, and a children list whose per-child scopes follow
`Generator.binderShifts`.

## Design summary

```
mk : (g : Generator) → g.payload scope → Children g.binderShifts scope → Flat scope
```

* `g : Generator` is the 74-summand enum from `Polygraph/Generator.lean`.
* `g.payload scope` is the per-generator non-recursive payload type:
  `Fin scope` for `gen_var`, `Nat` for `gen_universeCode`, and `Unit`
  for the remaining 72 ctors.
* `RawPolyTermFlatChildren g.binderShifts scope` is the children list
  indexed by `List Nat` of binder shifts and an outer scope; its `cons`
  head lives at `scope + shift`.

## Why honest-nested

The K11.8 mirror `RawPolyTerm` lists all 74 RawTerm-mirroring ctors
explicitly.  Every generic operation (rename, subst, parallel
reduction's confluence development `cd`) repeats the 74-arm cascade —
the per-ctor cascade tax that dominates kernel evolution.  The honest
nested form pushes the ctor enumeration INTO the `Generator` tag, so
the generic operations induct ONCE over `Generator` and consume
`children` uniformly.  Result: per-ctor cascade work collapses from
74 arms × N consumers to N consumers × 1 generic arm.

That is the substrate P2.4 (typed `PolyTerm` mirror), P2.8 (generic
`PolyTerm.rename` / `PolyTerm.subst`), and P3.5 (generic
`PolyStep.cd` / `cd_lemma`, which obsoletes every D2.5.x per-arm
cascade) ride on.

## Coexistence with legacy `RawPolyTerm`

This file does NOT delete or modify `LeanFX2.Foundation._deprecated_polygraph.RawPolyTerm`.
The legacy 74-ctor mirror keeps shipping; consumers continue to import
it as `Polygraph.RawPolyTerm`.  A follow-up slice will ship the
bidirectional bijection
`toLegacy : RawPolyTermFlat scope → RawPolyTerm scope` and
`fromLegacy : RawPolyTerm scope → RawPolyTermFlat scope` along with
the roundtrip lemmas, after which the typed-PolyTerm migration (P2.4
+ P2.6 + P2.7) can re-point through the honest substrate.

## Positivity

The mutual block's only cross-reference is
`RawPolyTermFlatChildren.cons`'s head field
`head : RawPolyTermFlat (scope + shift)`.  This is a direct field
occurrence (no function-spaces, no negative position), so Lean 4's
strict-positivity checker accepts the mutual block.

## Zero-axiom discipline

* Both inductives ship without `deriving DecidableEq` — equality
  decision across mutual indexed inductives with binder-shift indices
  is delicate and is deferred until a follow-up slice (after the
  bijection lands and tests can validate against the legacy
  `RawPolyTerm.decEq`).
* `Generator.payload` is a closed 74-arm match returning `Type`
  (constants `Fin scope`, `Nat`, `Unit`), so it admits `#print axioms`
  clean by `cases <;> rfl`-style structural reduction at every call
  site.
* The mutual inductive itself, declared in a `mutual` block with
  no Prop-valued indices, leaks no propext from its own definition. -/

namespace LeanFX2.Foundation._deprecated_polygraph

/-! ## Per-generator non-recursive payload table.

Returns the type of non-`RawPolyTermFlat`-recursive data carried by
the generator at the given scope.  Only two generators carry
non-trivial payload:

* `gen_var` carries a `Fin scope` (de Bruijn position).
* `gen_universeCode` carries a `Nat` (the inner universe level).

The remaining 72 generators carry `Unit` (no payload beyond the
children list).

This three-way classification mirrors the structure of `LeanFX2.RawTerm`:
two ctors with non-recursive payload, seventy-two purely recursive.

## Why `Unit` rather than splitting into a separate "atomic" enum

Returning `Unit` for the 72-of-74 majority lets the `mk` constructor
of `RawPolyTermFlat` have a uniform three-argument shape
`(g, payload, children)` regardless of which generator is being
applied.  Pattern-matching client code can ignore the payload via
the `()` wildcard when irrelevant.  A separate atomic enum would
add a discriminating case in every consumer — the precise cost the
polygraph re-foundation is trying to eliminate.

## Why all 74 arms enumerated explicitly (no wildcard)

A wildcard `_, _ => Unit` over the 74-ctor `Generator` triggers Lean
4's match compiler to emit propext-using equation lemmas for the
default case (see `feedback_lean_zero_axiom_match.md`).  Enumerating
all 74 arms keeps the match compiler in the "closed enum dispatch"
regime where every arm is a concrete constructor pattern, so no
auto-generated equation lemma needs `propext`.  The cost is 74 lines
of repetition — bought directly for zero-axiom hygiene. -/
def Generator.payload : Generator → Nat → Type
  -- Variable + unit
  | .gen_var, scope         => Fin scope
  | .gen_unit, _            => Unit
  -- Function
  | .gen_lam, _             => Unit
  | .gen_app, _             => Unit
  -- Pair
  | .gen_pair, _            => Unit
  | .gen_fst, _             => Unit
  | .gen_snd, _             => Unit
  -- Booleans
  | .gen_boolTrue, _        => Unit
  | .gen_boolFalse, _       => Unit
  | .gen_boolElim, _        => Unit
  -- Naturals
  | .gen_natZero, _         => Unit
  | .gen_natSucc, _         => Unit
  | .gen_natElim, _         => Unit
  | .gen_natRec, _          => Unit
  -- Lists
  | .gen_listNil, _         => Unit
  | .gen_listCons, _        => Unit
  | .gen_listElim, _        => Unit
  -- Options
  | .gen_optionNone, _      => Unit
  | .gen_optionSome, _      => Unit
  | .gen_optionMatch, _     => Unit
  -- Eithers
  | .gen_eitherInl, _       => Unit
  | .gen_eitherInr, _       => Unit
  | .gen_eitherMatch, _     => Unit
  -- Identity types
  | .gen_refl, _            => Unit
  | .gen_idJ, _             => Unit
  -- Modal
  | .gen_modIntro, _        => Unit
  | .gen_modElim, _         => Unit
  | .gen_subsume, _         => Unit
  -- Cubical interval
  | .gen_interval0, _       => Unit
  | .gen_interval1, _       => Unit
  | .gen_intervalOpp, _     => Unit
  | .gen_intervalMeet, _    => Unit
  | .gen_intervalJoin, _    => Unit
  -- Cubical path
  | .gen_pathLam, _         => Unit
  | .gen_pathApp, _         => Unit
  -- Cubical glue / transport / composition
  | .gen_glueIntro, _       => Unit
  | .gen_glueElim, _        => Unit
  | .gen_transp, _          => Unit
  | .gen_hcomp, _           => Unit
  -- Observational equality
  | .gen_oeqRefl, _         => Unit
  | .gen_oeqJ, _            => Unit
  | .gen_oeqFunext, _       => Unit
  -- Strict identity
  | .gen_idStrictRefl, _    => Unit
  | .gen_idStrictRec, _     => Unit
  -- Type equivalence
  | .gen_equivIntro, _      => Unit
  | .gen_equivApp, _        => Unit
  -- Refinement
  | .gen_refineIntro, _     => Unit
  | .gen_refineElim, _      => Unit
  -- Record
  | .gen_recordIntro, _     => Unit
  | .gen_recordProj, _      => Unit
  -- Codata
  | .gen_codataUnfold, _    => Unit
  | .gen_codataDest, _      => Unit
  -- Sessions
  | .gen_sessionSend, _     => Unit
  | .gen_sessionRecv, _     => Unit
  -- Effects
  | .gen_effectPerform, _   => Unit
  -- Universe code (inner level Nat payload)
  | .gen_universeCode, _    => Nat
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode, _       => Unit
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode, _        => Unit
  | .gen_sigmaTyCode, _     => Unit
  -- More atom-shape codes
  | .gen_productCode, _     => Unit
  | .gen_sumCode, _         => Unit
  | .gen_listCode, _        => Unit
  | .gen_optionCode, _      => Unit
  | .gen_eitherCode, _      => Unit
  | .gen_idCode, _          => Unit
  | .gen_equivCode, _       => Unit
  -- Cumulativity marker
  | .gen_cumulUpMarker, _   => Unit
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv, _       => Unit
  | .gen_equivApply, _      => Unit
  -- Composition vocabulary
  | .gen_pathCompose, _     => Unit
  | .gen_idToEquiv, _       => Unit
  | .gen_oeqTrans, _        => Unit
  | .gen_equivCompose, _    => Unit
  -- Cubical fill operation
  | .gen_transpFill, _      => Unit

/-! ## The honest nested inductive substrate.

`RawPolyTermFlat` is the polygraph dim-0 cell type indexed by a
single `Nat` scope.  Its single constructor `mk` carries:

1. The `Generator` tag selecting which RawTerm-equivalent ctor this
   cell encodes.
2. The per-generator `payload` (Fin position for var, Nat level for
   universeCode, Unit for everything else).
3. The recursive children list, indexed by `g.binderShifts` so each
   child's scope is the parent scope plus that child's binder shift.

`RawPolyTermFlatChildren` is the auxiliary list-indexed inductive
whose `cons` head lives at the parent scope augmented by the head
shift, and whose `tail` carries the remaining shifts and children.

## Worked examples

* `RawTerm.var p : RawTerm scope` corresponds to
  `mk .gen_var p .nil`
  (payload = `p : Fin scope`, children = empty list).
* `RawTerm.app f a : RawTerm scope` corresponds to
  `mk .gen_app () (.cons f (.cons a .nil))`
  (children at shifts `[0, 0]`, same scope).
* `RawTerm.lam body : RawTerm scope` (with `body : RawTerm (scope+1)`)
  corresponds to
  `mk .gen_lam () (.cons body .nil)`
  (single child at shift `[1]`, i.e. scope `scope + 1`).
* `RawTerm.piTyCode dom cod : RawTerm scope` (with `dom : RawTerm scope`,
  `cod : RawTerm (scope+1)`) corresponds to
  `mk .gen_piTyCode () (.cons dom (.cons cod .nil))`
  (children at shifts `[0, 1]`). -/
mutual
  inductive RawPolyTermFlat : Nat → Type where
    | mk {scope : Nat} (gen : Generator)
         (payload : gen.payload scope)
         (children : RawPolyTermFlatChildren gen.binderShifts scope) :
         RawPolyTermFlat scope

  inductive RawPolyTermFlatChildren :
      List Nat → Nat → Type where
    | nil  {scope : Nat} : RawPolyTermFlatChildren [] scope
    | cons {scope shift : Nat} {restShifts : List Nat}
           (head : RawPolyTermFlat (scope + shift))
           (tail : RawPolyTermFlatChildren restShifts scope) :
           RawPolyTermFlatChildren (shift :: restShifts) scope
end

/-! ## Smoke helpers — empty/singleton/binary/ternary children builders.

These are purely cosmetic helpers letting examples and downstream
proofs construct children lists without juggling the cons/nil
machinery.  Their existence in this file (rather than a separate
helpers file) keeps the polygraph substrate self-contained for the
P2.3 atomic ship.

Each helper is a definitional alias — `rfl` discharges its unfolding
at every call site. -/

/-- Empty children list at the given scope. -/
@[reducible] def RawPolyTermFlatChildren.empty (scope : Nat) :
    RawPolyTermFlatChildren [] scope :=
  .nil

/-- Singleton children list: one child at shift 0 (same scope). -/
@[reducible] def RawPolyTermFlatChildren.single
    {scope : Nat} (child : RawPolyTermFlat scope) :
    RawPolyTermFlatChildren [0] scope :=
  .cons child .nil

/-- Singleton children list under one fresh binder (shift 1). -/
@[reducible] def RawPolyTermFlatChildren.singleUnderBinder
    {scope : Nat} (body : RawPolyTermFlat (scope + 1)) :
    RawPolyTermFlatChildren [1] scope :=
  .cons body .nil

/-- Binary children list: both children at shift 0. -/
@[reducible] def RawPolyTermFlatChildren.pairFlat
    {scope : Nat}
    (firstChild secondChild : RawPolyTermFlat scope) :
    RawPolyTermFlatChildren [0, 0] scope :=
  .cons firstChild (.cons secondChild .nil)

/-- Binder-shape children list: first child at parent scope, second
under one fresh binder.  Used by `piTyCode` and `sigmaTyCode`. -/
@[reducible] def RawPolyTermFlatChildren.binderShape
    {scope : Nat}
    (domainPart : RawPolyTermFlat scope)
    (codomainPart : RawPolyTermFlat (scope + 1)) :
    RawPolyTermFlatChildren [0, 1] scope :=
  .cons domainPart (.cons codomainPart .nil)

/-- Ternary children list: three children at shift 0.  Used by all
ι-recursors (boolElim/natElim/listElim/optionMatch/eitherMatch/natRec)
and by `idCode`. -/
@[reducible] def RawPolyTermFlatChildren.tripleFlat
    {scope : Nat}
    (firstChild secondChild thirdChild : RawPolyTermFlat scope) :
    RawPolyTermFlatChildren [0, 0, 0] scope :=
  .cons firstChild (.cons secondChild (.cons thirdChild .nil))

end LeanFX2.Foundation._deprecated_polygraph

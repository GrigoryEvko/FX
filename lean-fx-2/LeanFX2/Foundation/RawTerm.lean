import LeanFX2.Foundation.Mode

/-! # RawTerm — Layer 0 untyped well-scoped terms.

`RawTerm scope` is the de Bruijn-indexed term family with `Fin scope`
positions for variables.  No types, no Ctx, no Ty references — pure
syntactic skeleton.

## Architectural role

RawTerm is the **type-level index** that makes lean-fx-2's Term
raw-aware.  Every Term ctor's signature pins the corresponding
RawTerm structure, so `Term.toRaw t = raw` is `rfl` (the projection
IS the type index).

## Constructors (28 total)

Mirrors lean-fx-2's typed Term constructor list (sans type
annotations).  Modal ctors (`modIntro`, `modElim`, `subsume`)
included from day 1 even though Layer 6 isn't implemented yet —
this avoids backward-incompatible additions later.

## Decidable equality

Auto-derived via `deriving DecidableEq`.  Per
`feedback_lean_zero_axiom_match.md` Rule 3 (full enumeration on
dependent inductive with universal Nat index), this is propext-free
in Lean 4 v4.29.1.
-/

namespace LeanFX2

/-- Untyped well-scoped terms.  De Bruijn variables via `Fin scope`. -/
inductive RawTerm : Nat → Type
  -- Variable
  | var {scope : Nat} (position : Fin scope) : RawTerm scope
  -- Unit
  | unit {scope : Nat} : RawTerm scope
  -- Function intro/elim (covers both arrow and Π applications)
  | lam {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope
  | app {scope : Nat} (functionTerm argumentTerm : RawTerm scope) : RawTerm scope
  -- Pair intro/elim (covers both non-dep and Σ)
  | pair {scope : Nat} (firstValue secondValue : RawTerm scope) : RawTerm scope
  | fst {scope : Nat} (pairTerm : RawTerm scope) : RawTerm scope
  | snd {scope : Nat} (pairTerm : RawTerm scope) : RawTerm scope
  -- Booleans
  | boolTrue {scope : Nat} : RawTerm scope
  | boolFalse {scope : Nat} : RawTerm scope
  | boolElim {scope : Nat}
      (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope
  -- Naturals
  | natZero {scope : Nat} : RawTerm scope
  | natSucc {scope : Nat} (predecessor : RawTerm scope) : RawTerm scope
  | natElim {scope : Nat}
      (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope
  | natRec {scope : Nat}
      (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope
  -- Lists
  | listNil {scope : Nat} : RawTerm scope
  | listCons {scope : Nat} (headTerm tailTerm : RawTerm scope) : RawTerm scope
  | listElim {scope : Nat}
      (scrutinee nilBranch consBranch : RawTerm scope) : RawTerm scope
  -- Options
  | optionNone {scope : Nat} : RawTerm scope
  | optionSome {scope : Nat} (valueTerm : RawTerm scope) : RawTerm scope
  | optionMatch {scope : Nat}
      (scrutinee noneBranch someBranch : RawTerm scope) : RawTerm scope
  -- Eithers
  | eitherInl {scope : Nat} (valueTerm : RawTerm scope) : RawTerm scope
  | eitherInr {scope : Nat} (valueTerm : RawTerm scope) : RawTerm scope
  | eitherMatch {scope : Nat}
      (scrutinee leftBranch rightBranch : RawTerm scope) : RawTerm scope
  -- Identity types
  | refl {scope : Nat} (rawWitness : RawTerm scope) : RawTerm scope
  | idJ {scope : Nat} (baseCase witness : RawTerm scope) : RawTerm scope
  -- Modal (Layer 6 references; raw-side ctors land from day 1)
  | modIntro {scope : Nat} (raw : RawTerm scope) : RawTerm scope
  | modElim {scope : Nat} (raw : RawTerm scope) : RawTerm scope
  | subsume {scope : Nat} (raw : RawTerm scope) : RawTerm scope
  deriving DecidableEq

end LeanFX2

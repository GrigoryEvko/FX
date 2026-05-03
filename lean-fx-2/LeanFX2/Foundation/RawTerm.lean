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
  -- D1.6 extension: 27 new ctors covering cubical / HOTT / refine /
  -- record / codata / session / effect / strict layers.  All are raw-
  -- syntactic skeletons; semantic interpretation lives in Reduction
  -- (D2.5–D2.7) and the typed Term inductive (D1.9).
  -- Cubical interval endpoints + lattice operations
  | interval0 {scope : Nat} : RawTerm scope
  | interval1 {scope : Nat} : RawTerm scope
  | intervalOpp {scope : Nat} (intervalTerm : RawTerm scope) : RawTerm scope
  | intervalMeet {scope : Nat}
      (leftInterval rightInterval : RawTerm scope) : RawTerm scope
  | intervalJoin {scope : Nat}
      (leftInterval rightInterval : RawTerm scope) : RawTerm scope
  -- Cubical path types (intro = lambda over interval, elim = path application)
  | pathLam {scope : Nat} (body : RawTerm (scope + 1)) : RawTerm scope
  | pathApp {scope : Nat}
      (pathTerm intervalArg : RawTerm scope) : RawTerm scope
  -- Cubical glue + transport / composition
  | glueIntro {scope : Nat}
      (baseValue partialValue : RawTerm scope) : RawTerm scope
  | glueElim {scope : Nat} (gluedValue : RawTerm scope) : RawTerm scope
  | transp {scope : Nat}
      (path source : RawTerm scope) : RawTerm scope
  | hcomp {scope : Nat}
      (sides cap : RawTerm scope) : RawTerm scope
  -- Observational equality (set-level OEq) — refl, J eliminator, funext
  | oeqRefl {scope : Nat} (witness : RawTerm scope) : RawTerm scope
  | oeqJ {scope : Nat}
      (baseCase witness : RawTerm scope) : RawTerm scope
  | oeqFunext {scope : Nat}
      (pointwiseEquality : RawTerm scope) : RawTerm scope
  -- Strict (definitional) identity — refl + eliminator
  | idStrictRefl {scope : Nat} (witness : RawTerm scope) : RawTerm scope
  | idStrictRec {scope : Nat}
      (baseCase witness : RawTerm scope) : RawTerm scope
  -- Type equivalence (Equiv A B) — intro from a function + inverse
  | equivIntro {scope : Nat}
      (forwardFn backwardFn : RawTerm scope) : RawTerm scope
  | equivApp {scope : Nat}
      (equivTerm argument : RawTerm scope) : RawTerm scope
  -- Refinement types — bundle a value with its predicate proof
  | refineIntro {scope : Nat}
      (rawValue predicateProof : RawTerm scope) : RawTerm scope
  | refineElim {scope : Nat} (refinedValue : RawTerm scope) : RawTerm scope
  -- Record types — single-field placeholder (multi-field via nesting)
  | recordIntro {scope : Nat} (firstField : RawTerm scope) : RawTerm scope
  | recordProj {scope : Nat} (recordValue : RawTerm scope) : RawTerm scope
  -- Codata — corecursive constructor + destructor
  | codataUnfold {scope : Nat}
      (initialState transition : RawTerm scope) : RawTerm scope
  | codataDest {scope : Nat} (codataValue : RawTerm scope) : RawTerm scope
  -- Session-typed channels — send / receive / end
  | sessionSend {scope : Nat}
      (channel payload : RawTerm scope) : RawTerm scope
  | sessionRecv {scope : Nat} (channel : RawTerm scope) : RawTerm scope
  -- Algebraic effect operation — perform an effect at runtime
  | effectPerform {scope : Nat}
      (operationTag arguments : RawTerm scope) : RawTerm scope
  deriving DecidableEq

end LeanFX2

import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.Kernel.Grade
import FX.Kernel.Level

/-!
# Mode-indexed and well-scoped kernel `Term` (V1a / W2)

The MTT-spine kernel's term inductive, indexed by the size of
the de Bruijn context.  Builds on the V1.3 mode-indexed Term by
adding a `Nat` index that bounds variable references — `Term n`
is a term in a context with `n` free variables.

## What W2 changes vs V1.3

V1.3 Term used `Nat` for the de Bruijn index of `var`, and the
checker (V1.5) was responsible for verifying every index was
in-range and every binder body lived in the correctly-extended
context.  W2 makes both invariants type-level:

  * `var : Mode → Fin n → Term n` — the index is a `Fin n`, so
    out-of-range indices are not Lean values.  Constructing a
    var at idx ≥ n is a Lean type error, not a checker
    rejection.
  * `lam : ... → Term n → Term (n+1) → Term n` — the body lives
    in the context extended by the bound variable.  Lean's type
    checker enforces "body sees one more binder than the
    surrounding context."
  * `pi`, `sigma`, `modElim` extend context similarly.

This is the V1a foundation per the architectural commitment:
making well-scopedness a type-level Lean invariant removes that
obligation from the checker, shrinking the trusted base.

Mode is still runtime data on every binder (V1.3 design choice).
Adding intrinsic mode indexing (`Term : Mode → Nat → Type`) is a
follow-on V1a extension; W2 limits scope to context-size only so
the mode-coherence work and the well-scoping work are
separable.

## Mutual inductive: Term + TermArgs

Lean 4 forbids nested inductive types where the nested type's
parameter contains a local variable of the outer inductive —
`List (Term n)` is rejected because `n` varies across
constructors.  The canonical workaround is a mutual inductive
with a custom list type; we name ours `TermArgs n`.

`TermArgs n` is structurally a `List (Term n)`: `nil` and `cons`
constructors with the standard semantics.  `TermArgs.ofList` /
`TermArgs.toList` convert in/out of `List (Term n)` for callers
that prefer the standard list API.

A `Coe (List (Term n)) (TermArgs n)` instance auto-coerces list
literals at constructor sites — `Term.ind m "Nat" []` and
`Term.ind m "List" [natType m]` work without explicit
conversion.

## Design choice: mode runtime, scope type-level

  * **Mode** stays runtime — `lam` carries `Mode` as a field,
    not as an index.  Mode coherence (e.g. lam at Software has
    a Software body) is still enforced by the checker in V1.5.
    Reasoning: keeping the V1.13 byte-identical conformance
    gate against the legacy mode-flat kernel tractable; mode is
    an informative tag but doesn't change the term's structural
    shape, so layering it as a type index would inflate the
    encoding without payoff at this stage.
  * **Scope** moves to type-level — `Fin n` for variables,
    `Term (n+1)` for binder bodies.  Reasoning: well-scopedness
    is a *structural* property the type system can enforce
    without paying the GADT cost of full intrinsic typing.  The
    checker no longer needs an `inRange` predicate.

## What stays from V1.3

Same 24 constructors; same mode-projection rule (cross-mode
constructors project the target mode); same HIT-replaces-Quot
choice; same name-indirection for `ind`/`coind`/`hit` specs;
same `coerceCell` 2-cell coercion node; same zero-`sorry` /
zero-axiom discipline.

## Trust layer

`FX/KernelMTT/**` is UNTRUSTED scaffold during Phase R1.  This
file commits to zero `sorry`, zero new axioms.  `structEq` and
`structEqArgs` are `partial def` (mutual) — same pattern as
legacy and V1.3.

## Cross-references

  * `fx_modecat.md` §2 — Mode 0-cells
  * `fx_modecat.md` §3 — Modality 1-cells
  * `fx_design.md` §6.10 — surface forms (`later`, `bridge`,
    `cap`, `transport`) that lower to `modIntro` / `modElim`
  * `fx_design.md` §30 — kernel calculus + Appendix H axioms
  * `FX/Kernel/Term.lean` — legacy mode-flat counterpart (uses
    bare `List Term` since it is not indexed)
  * `FX/KernelMTT/ModalityOps.lean` — operations layer over
    Term that threads the same context-size index
-/

namespace FX.KernelMTT

open FX.Kernel  -- Grade, Level, Effect (re-exported via Grade)

mutual

/-- Mode-indexed, well-scoped kernel term forms.  `Term n`
    denotes a term living in a de Bruijn context of size `n`.
    Constructors that bind a variable extend their body's
    context by 1.  The `Mode` field on each constructor stays
    runtime data per the V1.3 design; well-scopedness is the
    W2 invariant the type system enforces. -/
inductive Term : Nat → Type where
  /-- De Bruijn variable at `mode`.  The index is `Fin n`, so
      it is statically in range. -/
  | var {n : Nat} (mode : Mode) (deBruijnIndex : Fin n) : Term n
  /-- Function application at `mode`. -/
  | app {n : Nat} (mode : Mode)
        (funcTerm argTerm : Term n) : Term n
  /-- Graded lambda abstraction at `mode`.  Body in the context
      extended by the bound variable. -/
  | lam {n : Nat} (mode : Mode) (grade : Grade)
        (domain : Term n) (body : Term (n+1)) : Term n
  /-- Graded dependent function type with effect annotation. -/
  | pi {n : Nat} (mode : Mode) (grade : Grade)
       (domain : Term n) (body : Term (n+1))
       (returnEffect : Effect) : Term n
  /-- Graded dependent pair type at `mode`. -/
  | sigma {n : Nat} (mode : Mode) (grade : Grade)
          (domain : Term n) (body : Term (n+1)) : Term n
  /-- Universe at `universeLevel`, observed from `mode`. -/
  | type {n : Nat} (mode : Mode) (universeLevel : Level) : Term n
  /-- Universal level quantifier at `mode`.  Levels are a
      separate kind from terms; this binder doesn't extend the
      *term* context, so body lives at `Term n`. -/
  | forallLevel {n : Nat} (mode : Mode) (body : Term n) : Term n
  /-- Named reference to a top-level declaration at `mode`. -/
  | const {n : Nat} (mode : Mode) (name : String) : Term n
  /-- Applied inductive type at `mode`, by-name reference. -/
  | ind {n : Nat} (mode : Mode) (typeName : String)
        (typeArgs : TermArgs n) : Term n
  /-- Inductive constructor at `mode`. -/
  | ctor {n : Nat} (mode : Mode) (typeName : String)
         (ctorIndex : Nat)
         (typeArgs : TermArgs n)
         (valueArgs : TermArgs n) : Term n
  /-- Inductive recursor at `mode`. -/
  | indRec {n : Nat} (mode : Mode) (typeName : String)
           (motive : Term n)
           (methods : TermArgs n)
           (target : Term n) : Term n
  /-- Applied coinductive type at `mode`. -/
  | coind {n : Nat} (mode : Mode) (typeName : String)
          (typeArgs : TermArgs n) : Term n
  /-- Coinductive intro (`unfold`). -/
  | coindUnfold {n : Nat} (mode : Mode) (typeName : String)
                (typeArgs : TermArgs n)
                (arms : TermArgs n) : Term n
  /-- Coinductive single-destructor observation at `mode`. -/
  | coindDestruct {n : Nat} (mode : Mode) (typeName : String)
                  (destructorIndex : Nat)
                  (target : Term n) : Term n
  /-- Identity type at `mode`. -/
  | id {n : Nat} (mode : Mode)
       (baseType leftTerm rightTerm : Term n) : Term n
  /-- Identity introduction (`refl`) at `mode`. -/
  | refl {n : Nat} (mode : Mode) (witness : Term n) : Term n
  /-- Identity elimination (`J`, path induction) at `mode`. -/
  | idJ {n : Nat} (mode : Mode)
        (motive base eqProof : Term n) : Term n
  /-- Higher inductive type at `mode`. -/
  | hit {n : Nat} (mode : Mode) (typeName : String)
        (typeArgs : TermArgs n) : Term n
  /-- HIT data constructor (parallel to `ctor`). -/
  | hitMk {n : Nat} (mode : Mode) (typeName : String)
          (ctorIndex : Nat)
          (typeArgs : TermArgs n)
          (valueArgs : TermArgs n) : Term n
  /-- HIT eliminator. -/
  | hitRec {n : Nat} (mode : Mode) (typeName : String)
           (motive : Term n)
           (dataMethods : TermArgs n)
           (pathProofs : TermArgs n)
           (target : Term n) : Term n
  /-- Modality introduction across modes. -/
  | modIntro {n : Nat} (sourceMode targetMode : Mode)
             (modality : Modality)
             (term : Term n) : Term n
  /-- Modality elimination.  Body in extended context. -/
  | modElim {n : Nat} (sourceMode targetMode : Mode)
            (modality : Modality)
            (modalTerm : Term n)
            (body : Term (n+1)) : Term n
  /-- Wire-boundary equivalence transport. -/
  | transport {n : Nat} (equivProof source : Term n) : Term n
  /-- 2-cell subsumption coercion.  Mode preserved across the
      coercion (cells are within-modality / within-mode); the
      result mode equals the underlying `term`'s mode. -/
  | coerceCell {n : Nat} (modality : Modality)
               (fromGrade toGrade : String)
               (term : Term n) : Term n

/-- Well-scoped argument list for `Term` constructors that take
    a variable-arity arg list (`ind`, `ctor`, `indRec`, `coind`,
    `coindUnfold`, `hit`, `hitMk`, `hitRec`).

    Mutual with `Term` because Lean 4 forbids nested inductive
    types whose parameters contain local variables of the outer
    inductive (`List (Term n)` is rejected; `TermArgs n` is
    accepted as a mutual peer). -/
inductive TermArgs : Nat → Type where
  /-- Empty argument list. -/
  | nil  {n : Nat} : TermArgs n
  /-- Argument list cons. -/
  | cons {n : Nat} (head : Term n) (tail : TermArgs n) : TermArgs n

end

/-- Default inhabitant — the simplest closed form, the static-
    layer Type at level 0.  Polymorphic in the context size
    because `.type` carries no `Term n` subterms. -/
instance {n : Nat} : Inhabited (Term n) :=
  ⟨Term.type Mode.ghost Level.zero⟩

/-- Default inhabitant for `TermArgs n` is the empty argument
    list. -/
instance {n : Nat} : Inhabited (TermArgs n) :=
  ⟨TermArgs.nil⟩

namespace TermArgs

/-- Convert a `List (Term n)` to a `TermArgs n`.  Used at test
    sites and elsewhere that prefer standard list syntax. -/
def ofList {n : Nat} : List (Term n) → TermArgs n
  | []      => .nil
  | x :: xs => .cons x (ofList xs)

/-- Convert a `TermArgs n` back to `List (Term n)`. -/
def toList {n : Nat} : TermArgs n → List (Term n)
  | .nil       => []
  | .cons x xs => x :: toList xs

/-- Length of an argument list. -/
def length {n : Nat} : TermArgs n → Nat
  | .nil       => 0
  | .cons _ xs => length xs + 1

end TermArgs

/-- Auto-coerce list literals to `TermArgs` at constructor
    sites.  Lets callers write `Term.ind m "Nat" []` and
    `Term.ctor m "Bool" 1 [] []` without explicit
    `TermArgs.ofList` boilerplate. -/
instance {n : Nat} : Coe (List (Term n)) (TermArgs n) where
  coe := TermArgs.ofList

namespace Term

/-- Project the mode of a term.  Same dispatch as V1.3:
    binder constructors project their `mode` field; cross-mode
    constructors project the TARGET mode; `transport` always
    `Mode.wire`; `coerceCell` preserves the inner term's mode. -/
def mode {n : Nat} : Term n → Mode
  | .var m _                             => m
  | .app m _ _                           => m
  | .lam m _ _ _                         => m
  | .pi m _ _ _ _                        => m
  | .sigma m _ _ _                       => m
  | .type m _                            => m
  | .forallLevel m _                     => m
  | .const m _                           => m
  | .ind m _ _                           => m
  | .ctor m _ _ _ _                      => m
  | .indRec m _ _ _ _                    => m
  | .coind m _ _                         => m
  | .coindUnfold m _ _ _                 => m
  | .coindDestruct m _ _ _               => m
  | .id m _ _ _                          => m
  | .refl m _                            => m
  | .idJ m _ _ _                         => m
  | .hit m _ _                           => m
  | .hitMk m _ _ _ _                     => m
  | .hitRec m _ _ _ _ _                  => m
  | .modIntro _ targetMode _ _           => targetMode
  | .modElim _ targetMode _ _ _          => targetMode
  | .transport _ _                       => Mode.wire
  | .coerceCell _ _ _ inner              => inner.mode

/- Structural equality on well-scoped terms.  Both sides must
   live at the same context size; recursion through binders
   implicitly works at `n+1`.  Mutual with `structEqArgs` for
   the variable-arity argument lists.

   `partial def` because Term recurses through `TermArgs n`
   in several constructors and Lean's auto-deriving of
   DecidableEq doesn't handle that combined with the Grade
   field.  `Grade.beq` handles Grade comparison; `decide`
   handles Mode, Modality, Level, Effect. -/

mutual

partial def structEq {n : Nat} : Term n → Term n → Bool
  | .var lMode lIdx, .var rMode rIdx =>
    decide (lMode = rMode) && lIdx == rIdx
  | .app lMode lFn lArg, .app rMode rFn rArg =>
    decide (lMode = rMode)
      && structEq lFn rFn && structEq lArg rArg
  | .lam lMode lGrade lTy lBody, .lam rMode rGrade rTy rBody =>
    decide (lMode = rMode) && Grade.beq lGrade rGrade
      && structEq lTy rTy && structEq lBody rBody
  | .pi lMode lGrade lTy lBody lEff,
    .pi rMode rGrade rTy rBody rEff =>
    decide (lMode = rMode) && Grade.beq lGrade rGrade
      && structEq lTy rTy && structEq lBody rBody
      && decide (lEff = rEff)
  | .sigma lMode lGrade lTy lBody,
    .sigma rMode rGrade rTy rBody =>
    decide (lMode = rMode) && Grade.beq lGrade rGrade
      && structEq lTy rTy && structEq lBody rBody
  | .type lMode lLevel, .type rMode rLevel =>
    decide (lMode = rMode) && decide (lLevel = rLevel)
  | .forallLevel lMode lBody, .forallLevel rMode rBody =>
    decide (lMode = rMode) && structEq lBody rBody
  | .const lMode lName, .const rMode rName =>
    decide (lMode = rMode) && lName == rName
  | .ind lMode lName lArgs, .ind rMode rName rArgs =>
    decide (lMode = rMode) && lName == rName
      && structEqArgs lArgs rArgs
  | .ctor lMode lName lIdx lTArgs lArgs,
    .ctor rMode rName rIdx rTArgs rArgs =>
    decide (lMode = rMode) && lName == rName && lIdx == rIdx
      && structEqArgs lTArgs rTArgs
      && structEqArgs lArgs rArgs
  | .indRec lMode lName lMot lMethods lTarget,
    .indRec rMode rName rMot rMethods rTarget =>
    decide (lMode = rMode) && lName == rName
      && structEq lMot rMot
      && structEqArgs lMethods rMethods
      && structEq lTarget rTarget
  | .coind lMode lName lArgs, .coind rMode rName rArgs =>
    decide (lMode = rMode) && lName == rName
      && structEqArgs lArgs rArgs
  | .coindUnfold lMode lName lTArgs lArms,
    .coindUnfold rMode rName rTArgs rArms =>
    decide (lMode = rMode) && lName == rName
      && structEqArgs lTArgs rTArgs
      && structEqArgs lArms rArms
  | .coindDestruct lMode lName lIdx lTarget,
    .coindDestruct rMode rName rIdx rTarget =>
    decide (lMode = rMode) && lName == rName && lIdx == rIdx
      && structEq lTarget rTarget
  | .id lMode lTy lLhs lRhs, .id rMode rTy rLhs rRhs =>
    decide (lMode = rMode)
      && structEq lTy rTy
      && structEq lLhs rLhs
      && structEq lRhs rRhs
  | .refl lMode lW, .refl rMode rW =>
    decide (lMode = rMode) && structEq lW rW
  | .idJ lMode lMot lBase lEq, .idJ rMode rMot rBase rEq =>
    decide (lMode = rMode)
      && structEq lMot rMot
      && structEq lBase rBase
      && structEq lEq rEq
  | .hit lMode lName lArgs, .hit rMode rName rArgs =>
    decide (lMode = rMode) && lName == rName
      && structEqArgs lArgs rArgs
  | .hitMk lMode lName lIdx lTArgs lArgs,
    .hitMk rMode rName rIdx rTArgs rArgs =>
    decide (lMode = rMode) && lName == rName && lIdx == rIdx
      && structEqArgs lTArgs rTArgs
      && structEqArgs lArgs rArgs
  | .hitRec lMode lName lMot lDataM lPathP lTarget,
    .hitRec rMode rName rMot rDataM rPathP rTarget =>
    decide (lMode = rMode) && lName == rName
      && structEq lMot rMot
      && structEqArgs lDataM rDataM
      && structEqArgs lPathP rPathP
      && structEq lTarget rTarget
  | .modIntro lSrc lTgt lMod lT,
    .modIntro rSrc rTgt rMod rT =>
    decide (lSrc = rSrc) && decide (lTgt = rTgt)
      && decide (lMod = rMod)
      && structEq lT rT
  | .modElim lSrc lTgt lMod lTerm lBody,
    .modElim rSrc rTgt rMod rTerm rBody =>
    decide (lSrc = rSrc) && decide (lTgt = rTgt)
      && decide (lMod = rMod)
      && structEq lTerm rTerm
      && structEq lBody rBody
  | .transport lE lS, .transport rE rS =>
    structEq lE rE && structEq lS rS
  | .coerceCell lMod lFrom lTo lTerm,
    .coerceCell rMod rFrom rTo rTerm =>
    decide (lMod = rMod) && lFrom == rFrom && lTo == rTo
      && structEq lTerm rTerm
  | _, _ => false

/-- Pointwise `structEq` over two argument lists at the same
    context size. -/
partial def structEqArgs {n : Nat} :
    TermArgs n → TermArgs n → Bool
  | .nil, .nil => true
  | .cons l ls, .cons r rs =>
    structEq l r && structEqArgs ls rs
  | _, _ => false

end

instance {n : Nat} : BEq (Term n) := ⟨structEq⟩

/-- Construct a totally-pure `Pi` at the runtime layer (Software
    mode) — the most-common case.  Body lives in the context
    extended by the domain binder. -/
abbrev piTotSoftware {n : Nat} (grade : Grade)
    (domain : Term n) (body : Term (n+1)) : Term n :=
  Term.pi Mode.software grade domain body Effect.tot

/-- Construct a totally-pure `Pi` at the static (proof-only)
    layer (Ghost mode).  The proof-level analogue of
    `piTotSoftware`. -/
abbrev piTotGhost {n : Nat} (grade : Grade)
    (domain : Term n) (body : Term (n+1)) : Term n :=
  Term.pi Mode.ghost grade domain body Effect.tot

end Term

end FX.KernelMTT

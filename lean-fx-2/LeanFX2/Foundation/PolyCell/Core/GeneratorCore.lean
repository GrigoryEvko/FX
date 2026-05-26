/-! # Foundation/PolyCell/Core/GeneratorCore — Term-free Generator substrate

The 74-summand Generator enum + arity + binderShifts + discipline lemma,
factored out of the deprecated _deprecated_polygraph/Generator.lean to remove
the LeanFX2.Term import dependency.  This is the Allais universe-of-syntaxes
descriptor carrier (arXiv:2001.11001) that every PolyCell v2 layer inducts
over ONCE.  No import beyond Init. -/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Full 74-summand polygraph generator enum.  Mirrors
`LeanFX2.RawTerm`'s 74 constructors one-to-one (see
`Foundation/RawTerm.lean`).  Grouped by family with comments
matching the RawTerm source's grouping.

Each Generator name is the RawTerm ctor name prefixed with
`gen_`.  This preserves the bijection at the name level: a
reader who knows RawTerm's vocabulary recognizes every summand
immediately. -/
inductive Generator : Type
  -- Variable + unit
  | gen_var
  | gen_unit
  -- Function intro/elim (covers arrow and Π applications)
  | gen_lam
  | gen_app
  -- Pair intro/elim (covers non-dep and Σ)
  | gen_pair
  | gen_fst
  | gen_snd
  -- Booleans
  | gen_boolTrue
  | gen_boolFalse
  | gen_boolElim
  -- Naturals
  | gen_natZero
  | gen_natSucc
  | gen_natElim
  | gen_natRec
  -- Lists
  | gen_listNil
  | gen_listCons
  | gen_listElim
  -- Options
  | gen_optionNone
  | gen_optionSome
  | gen_optionMatch
  -- Eithers
  | gen_eitherInl
  | gen_eitherInr
  | gen_eitherMatch
  -- Identity types
  | gen_refl
  | gen_idJ
  -- Modal (Layer 6 references; raw-side ctors land from day 1)
  | gen_modIntro
  | gen_modElim
  | gen_subsume
  -- Cubical interval endpoints + lattice operations
  | gen_interval0
  | gen_interval1
  | gen_intervalOpp
  | gen_intervalMeet
  | gen_intervalJoin
  -- Cubical path types (intro = lambda over interval, elim = path app)
  | gen_pathLam
  | gen_pathApp
  -- Cubical glue + transport / composition
  | gen_glueIntro
  | gen_glueElim
  | gen_transp
  | gen_hcomp
  -- Observational equality (set-level OEq) — refl, J eliminator, funext
  | gen_oeqRefl
  | gen_oeqJ
  | gen_oeqFunext
  -- Strict (definitional) identity — refl + eliminator
  | gen_idStrictRefl
  | gen_idStrictRec
  -- Type equivalence
  | gen_equivIntro
  | gen_equivApp
  -- Refinement types
  | gen_refineIntro
  | gen_refineElim
  -- Record types
  | gen_recordIntro
  | gen_recordProj
  -- Codata
  | gen_codataUnfold
  | gen_codataDest
  -- Session-typed channels
  | gen_sessionSend
  | gen_sessionRecv
  -- Algebraic effects
  | gen_effectPerform
  -- Universe-code term (innerLevel : Nat payload, no RawTerm children)
  | gen_universeCode
  -- CUMUL-2.1: per-shape type-code constructors (atom-shape)
  | gen_arrowCode
  -- CUMUL-2.1: per-shape type-code constructors (binder-shape)
  | gen_piTyCode
  | gen_sigmaTyCode
  -- CUMUL-2.1: more atom-shape codes
  | gen_productCode
  | gen_sumCode
  | gen_listCode
  | gen_optionCode
  | gen_eitherCode
  | gen_idCode
  | gen_equivCode
  -- CUMUL-2.6: cumulativity marker
  | gen_cumulUpMarker
  -- D3.6-P1/P2: univalence-to-equiv vocabulary
  | gen_uaToEquiv
  | gen_equivApply
  -- D3.6-S3/S4/S5: cubical/HOTT composition vocabulary
  | gen_pathCompose
  | gen_idToEquiv
  | gen_oeqTrans
  | gen_equivCompose
  -- D2.5.6-Blocker-A: cubical fill operation
  | gen_transpFill
  deriving DecidableEq

/-- The child count per `Generator`.  Each entry equals the
number of `RawTerm`-valued payload fields in the corresponding
`RawTerm` constructor.  `var` carries a `Fin scope` position but
that does NOT count as a child (it lives at the variable layer,
not the polygraph fold input).  `universeCode` carries a `Nat`
payload, similarly not a child. -/
def Generator.arity : Generator → Nat
  -- Variable + unit (no RawTerm children)
  | .gen_var          => 0  -- Fin scope payload, not a child
  | .gen_unit         => 0
  -- Function
  | .gen_lam          => 1  -- body
  | .gen_app          => 2  -- functionTerm, argumentTerm
  -- Pair
  | .gen_pair         => 2  -- firstValue, secondValue
  | .gen_fst          => 1  -- pairTerm
  | .gen_snd          => 1  -- pairTerm
  -- Booleans
  | .gen_boolTrue     => 0
  | .gen_boolFalse    => 0
  | .gen_boolElim     => 3  -- scrutinee, thenBranch, elseBranch
  -- Naturals
  | .gen_natZero      => 0
  | .gen_natSucc      => 1  -- predecessor
  | .gen_natElim      => 3  -- scrutinee, zeroBranch, succBranch
  | .gen_natRec       => 3  -- scrutinee, zeroBranch, succBranch
  -- Lists
  | .gen_listNil      => 0
  | .gen_listCons     => 2  -- headTerm, tailTerm
  | .gen_listElim     => 3  -- scrutinee, nilBranch, consBranch
  -- Options
  | .gen_optionNone   => 0
  | .gen_optionSome   => 1  -- valueTerm
  | .gen_optionMatch  => 3  -- scrutinee, noneBranch, someBranch
  -- Eithers
  | .gen_eitherInl    => 1  -- valueTerm
  | .gen_eitherInr    => 1  -- valueTerm
  | .gen_eitherMatch  => 3  -- scrutinee, leftBranch, rightBranch
  -- Identity types
  | .gen_refl         => 1  -- rawWitness
  | .gen_idJ          => 2  -- baseCase, witness
  -- Modal
  | .gen_modIntro     => 1  -- raw
  | .gen_modElim      => 1  -- raw
  | .gen_subsume      => 1  -- raw
  -- Cubical interval
  | .gen_interval0    => 0
  | .gen_interval1    => 0
  | .gen_intervalOpp  => 1  -- intervalTerm
  | .gen_intervalMeet => 2  -- leftInterval, rightInterval
  | .gen_intervalJoin => 2  -- leftInterval, rightInterval
  -- Cubical path
  | .gen_pathLam      => 1  -- body
  | .gen_pathApp      => 2  -- pathTerm, intervalArg
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => 2  -- baseValue, partialValue
  | .gen_glueElim     => 1  -- gluedValue
  | .gen_transp       => 2  -- path, source
  | .gen_hcomp        => 2  -- sides, cap
  -- Observational equality
  | .gen_oeqRefl      => 1  -- witness
  | .gen_oeqJ         => 2  -- baseCase, witness
  | .gen_oeqFunext    => 1  -- pointwiseEquality
  -- Strict identity
  | .gen_idStrictRefl => 1  -- witness
  | .gen_idStrictRec  => 2  -- baseCase, witness
  -- Type equivalence
  | .gen_equivIntro   => 2  -- forwardFn, backwardFn
  | .gen_equivApp     => 2  -- equivTerm, argument
  -- Refinement
  | .gen_refineIntro  => 2  -- rawValue, predicateProof
  | .gen_refineElim   => 1  -- refinedValue
  -- Record
  | .gen_recordIntro  => 1  -- firstField
  | .gen_recordProj   => 1  -- recordValue
  -- Codata
  | .gen_codataUnfold => 2  -- initialState, transition
  | .gen_codataDest   => 1  -- codataValue
  -- Sessions
  | .gen_sessionSend  => 2  -- channel, payload
  | .gen_sessionRecv  => 1  -- channel
  -- Effects
  | .gen_effectPerform => 2 -- operationTag, arguments
  -- Universe code (Nat payload, no RawTerm children)
  | .gen_universeCode => 0
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    => 2  -- domainCode, codomainCode
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode     => 2  -- domainCode, codomainCode (codomain at scope+1)
  | .gen_sigmaTyCode  => 2  -- domainCode, codomainCode (codomain at scope+1)
  -- More atom-shape codes
  | .gen_productCode  => 2  -- firstCode, secondCode
  | .gen_sumCode      => 2  -- leftCode, rightCode
  | .gen_listCode     => 1  -- elementCode
  | .gen_optionCode   => 1  -- elementCode
  | .gen_eitherCode   => 2  -- leftCode, rightCode
  | .gen_idCode       => 3  -- typeCode, leftRaw, rightRaw
  | .gen_equivCode    => 2  -- leftTypeCode, rightTypeCode
  -- Cumulativity marker
  | .gen_cumulUpMarker => 1 -- innerCodeRaw
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => 1  -- proofRaw
  | .gen_equivApply   => 2  -- equivRaw, argRaw
  -- Composition vocabulary
  | .gen_pathCompose  => 2  -- leftPathRaw, rightPathRaw
  | .gen_idToEquiv    => 1  -- proofRaw
  | .gen_oeqTrans     => 2  -- firstProof, secondProof
  | .gen_equivCompose => 2  -- firstEquiv, secondEquiv
  -- Cubical fill
  | .gen_transpFill   => 3  -- pathTy, currentInterval, source

/-- The per-child binder shifts as a non-dependent `List Nat`
table.  The list length equals `Generator.arity g` (by
construction, verified by `binderShifts_length_eq_arity`).  Each
list entry is the number of fresh binders introduced over the
corresponding child.

**Non-zero entries** (only four constructors carry binders):

* `gen_lam` — body lives under one fresh value binder, shift `1`.
* `gen_pathLam` — body lives under one fresh interval binder,
  shift `1`.
* `gen_piTyCode` — codomain lives at `scope + 1`, shift on the
  second child is `1`.  Mirrors `RawTerm.piTyCode`'s codomain
  index.
* `gen_sigmaTyCode` — codomain lives at `scope + 1`, shift on the
  second child is `1`.  Mirrors `RawTerm.sigmaTyCode`'s codomain
  index.

All other ctors have all-zero shifts.

**Why a `List Nat` rather than `Fin g.arity → Nat`**:
indexed-by-arity-zero Fin destructuring leaks propext via Lean's
match compilation (see `feedback_lean_zero_axiom_match.md`).
Returning a `List Nat` keeps the function arity-independent at the
type level, so each arm is a closed term — no dependent reduction,
no propext.  The length-check theorem
`binderShifts_length_eq_arity` recovers the total-function
discipline. -/
def Generator.binderShifts : Generator → List Nat
  -- Variable + unit
  | .gen_var          => []
  | .gen_unit         => []
  -- Function
  | .gen_lam          => [1]                 -- body under one fresh binder
  | .gen_app          => [0, 0]
  -- Pair
  | .gen_pair         => [0, 0]
  | .gen_fst          => [0]
  | .gen_snd          => [0]
  -- Booleans
  | .gen_boolTrue     => []
  | .gen_boolFalse    => []
  | .gen_boolElim     => [0, 0, 0]
  -- Naturals
  | .gen_natZero      => []
  | .gen_natSucc      => [0]
  | .gen_natElim      => [0, 0, 0]
  | .gen_natRec       => [0, 0, 0]
  -- Lists
  | .gen_listNil      => []
  | .gen_listCons     => [0, 0]
  | .gen_listElim     => [0, 0, 0]
  -- Options
  | .gen_optionNone   => []
  | .gen_optionSome   => [0]
  | .gen_optionMatch  => [0, 0, 0]
  -- Eithers
  | .gen_eitherInl    => [0]
  | .gen_eitherInr    => [0]
  | .gen_eitherMatch  => [0, 0, 0]
  -- Identity types
  | .gen_refl         => [0]
  | .gen_idJ          => [0, 0]
  -- Modal
  | .gen_modIntro     => [0]
  | .gen_modElim      => [0]
  | .gen_subsume      => [0]
  -- Cubical interval
  | .gen_interval0    => []
  | .gen_interval1    => []
  | .gen_intervalOpp  => [0]
  | .gen_intervalMeet => [0, 0]
  | .gen_intervalJoin => [0, 0]
  -- Cubical path
  | .gen_pathLam      => [1]                 -- body under one fresh interval binder
  | .gen_pathApp      => [0, 0]
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => [0, 0]
  | .gen_glueElim     => [0]
  | .gen_transp       => [0, 0]
  | .gen_hcomp        => [0, 0]
  -- Observational equality
  | .gen_oeqRefl      => [0]
  | .gen_oeqJ         => [0, 0]
  | .gen_oeqFunext    => [0]
  -- Strict identity
  | .gen_idStrictRefl => [0]
  | .gen_idStrictRec  => [0, 0]
  -- Type equivalence
  | .gen_equivIntro   => [0, 0]
  | .gen_equivApp     => [0, 0]
  -- Refinement
  | .gen_refineIntro  => [0, 0]
  | .gen_refineElim   => [0]
  -- Record
  | .gen_recordIntro  => [0]
  | .gen_recordProj   => [0]
  -- Codata
  | .gen_codataUnfold => [0, 0]
  | .gen_codataDest   => [0]
  -- Sessions
  | .gen_sessionSend  => [0, 0]
  | .gen_sessionRecv  => [0]
  -- Effects
  | .gen_effectPerform => [0, 0]
  -- Universe code
  | .gen_universeCode => []
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    => [0, 0]
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode     => [0, 1]              -- codomain at scope + 1
  | .gen_sigmaTyCode  => [0, 1]              -- codomain at scope + 1
  -- More atom-shape codes
  | .gen_productCode  => [0, 0]
  | .gen_sumCode      => [0, 0]
  | .gen_listCode     => [0]
  | .gen_optionCode   => [0]
  | .gen_eitherCode   => [0, 0]
  | .gen_idCode       => [0, 0, 0]
  | .gen_equivCode    => [0, 0]
  -- Cumulativity marker
  | .gen_cumulUpMarker => [0]
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => [0]
  | .gen_equivApply   => [0, 0]
  -- Composition vocabulary
  | .gen_pathCompose  => [0, 0]
  | .gen_idToEquiv    => [0]
  | .gen_oeqTrans     => [0, 0]
  | .gen_equivCompose => [0, 0]
  -- Cubical fill
  | .gen_transpFill   => [0, 0, 0]

/-- The `binderShifts` table has length exactly `arity g`.
Proof is case-analysis on `g`; each of the 74 arms closes via
`rfl` (`[].length = 0`, `[x].length = 1`, etc.).  Recovers the
total-function discipline that a `Fin g.arity → Nat` signature
would carry at the type level (but at the cost of a propext
leak — see `binderShifts`'s docstring). -/
theorem Generator.binderShifts_length_eq_arity (g : Generator) :
    g.binderShifts.length = g.arity := by
  cases g <;> rfl

/-- Per-generator local-scalar payload type, indexed by scope.
`gen_var` maps to `Fin scope` (scope-safe BY CONSTRUCTION — the strict
improvement over v1's `index < scope` side-condition).  `gen_universeCode`
maps to `Nat` (the universe level).  All other 72 ctors map to `Unit`.
Full enumeration, no wildcard. -/
def Generator.payload : Generator → Nat → Type
  | .gen_var, scope => Fin scope
  | .gen_universeCode, _ => Nat
  | .gen_unit, _ => Unit
  | .gen_lam, _ => Unit
  | .gen_app, _ => Unit
  | .gen_pair, _ => Unit
  | .gen_fst, _ => Unit
  | .gen_snd, _ => Unit
  | .gen_boolTrue, _ => Unit
  | .gen_boolFalse, _ => Unit
  | .gen_boolElim, _ => Unit
  | .gen_natZero, _ => Unit
  | .gen_natSucc, _ => Unit
  | .gen_natElim, _ => Unit
  | .gen_natRec, _ => Unit
  | .gen_listNil, _ => Unit
  | .gen_listCons, _ => Unit
  | .gen_listElim, _ => Unit
  | .gen_optionNone, _ => Unit
  | .gen_optionSome, _ => Unit
  | .gen_optionMatch, _ => Unit
  | .gen_eitherInl, _ => Unit
  | .gen_eitherInr, _ => Unit
  | .gen_eitherMatch, _ => Unit
  | .gen_refl, _ => Unit
  | .gen_idJ, _ => Unit
  | .gen_modIntro, _ => Unit
  | .gen_modElim, _ => Unit
  | .gen_subsume, _ => Unit
  | .gen_interval0, _ => Unit
  | .gen_interval1, _ => Unit
  | .gen_intervalOpp, _ => Unit
  | .gen_intervalMeet, _ => Unit
  | .gen_intervalJoin, _ => Unit
  | .gen_pathLam, _ => Unit
  | .gen_pathApp, _ => Unit
  | .gen_glueIntro, _ => Unit
  | .gen_glueElim, _ => Unit
  | .gen_transp, _ => Unit
  | .gen_hcomp, _ => Unit
  | .gen_oeqRefl, _ => Unit
  | .gen_oeqJ, _ => Unit
  | .gen_oeqFunext, _ => Unit
  | .gen_idStrictRefl, _ => Unit
  | .gen_idStrictRec, _ => Unit
  | .gen_equivIntro, _ => Unit
  | .gen_equivApp, _ => Unit
  | .gen_refineIntro, _ => Unit
  | .gen_refineElim, _ => Unit
  | .gen_recordIntro, _ => Unit
  | .gen_recordProj, _ => Unit
  | .gen_codataUnfold, _ => Unit
  | .gen_codataDest, _ => Unit
  | .gen_sessionSend, _ => Unit
  | .gen_sessionRecv, _ => Unit
  | .gen_effectPerform, _ => Unit
  | .gen_arrowCode, _ => Unit
  | .gen_piTyCode, _ => Unit
  | .gen_sigmaTyCode, _ => Unit
  | .gen_productCode, _ => Unit
  | .gen_sumCode, _ => Unit
  | .gen_listCode, _ => Unit
  | .gen_optionCode, _ => Unit
  | .gen_eitherCode, _ => Unit
  | .gen_idCode, _ => Unit
  | .gen_equivCode, _ => Unit
  | .gen_cumulUpMarker, _ => Unit
  | .gen_uaToEquiv, _ => Unit
  | .gen_equivApply, _ => Unit
  | .gen_pathCompose, _ => Unit
  | .gen_idToEquiv, _ => Unit
  | .gen_oeqTrans, _ => Unit
  | .gen_equivCompose, _ => Unit
  | .gen_transpFill, _ => Unit

end LeanFX2.Foundation.PolyCell.Core

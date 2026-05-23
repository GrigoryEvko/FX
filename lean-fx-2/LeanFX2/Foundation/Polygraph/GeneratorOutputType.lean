import LeanFX2.Foundation.Polygraph.Generator

/-! # Foundation/Polygraph/GeneratorOutputType — accelerate-P2.2 (#2123).

The per-Generator output-type extractors.  Each function takes the
typed children of a Generator cell and computes the output `Ty`
CAST-FREE — the same pattern shown to work in `Generator.outputTypeAppPi`
(the P2.0 spike artifact).

## Coverage

The Π/Σ + closed-type-recursor families — 12 extractors mirroring
`Term`'s 12 corresponding ctors at `LeanFX2/Term.lean:104-234`:

**Π/Σ family** (6 extractors at `LeanFX2/Term.lean:104-146`):

* `outputTypeApp` — non-dependent function application:
  `Ty.arrow A B → A → B`.
* `outputTypeLam` — non-dependent function intro:
  `Term (ctx.cons A) B.weaken _ → Ty.arrow A B`.
* `outputTypeLamPi` — dependent function intro:
  `Term (ctx.cons A) B _ → Ty.piTy A B`.
* `outputTypePair` — dependent pair intro:
  `Term ctx A _ → Term ctx (B.subst0 A xRaw) _ → Ty.sigmaTy A B`.
* `outputTypeFst` — dependent pair first projection:
  `Term ctx (Ty.sigmaTy A B) _ → A`.
* `outputTypeSnd` — dependent pair second projection:
  `Term ctx (Ty.sigmaTy A B) pairRaw → B.subst0 A (RawTerm.fst pairRaw)`.

**Closed-type recursor family** (6 extractors at
`LeanFX2/Term.lean:152-234`):

* `outputTypeBoolElim` — dependent bool eliminator: motive lives at
  `Ty level (scope + 1)`; output is
  `motiveType.subst0 Ty.bool scrutineeRaw`.
* `outputTypeNatElim` — non-dependent nat eliminator: output is the
  motive `Ty level scope` itself.
* `outputTypeNatRec` — non-dependent nat recursor: output is the
  motive.
* `outputTypeListElim` — non-dependent list eliminator: output is
  the motive.
* `outputTypeOptionMatch` — non-dependent option matcher: output is
  the motive.
* `outputTypeEitherMatch` — non-dependent either matcher: output is
  the motive.

Plus the P2.0-shipped `outputTypeAppPi` (in `Generator.lean`) which
covers dependent function application.  Together these 13 extractors
cover the Π/Σ core + the closed-type recursor vocabulary of the
kernel (13 of 74 outputType ctors).

## Method

Each extractor follows the spike pattern: pull every typed child's
type indices via implicit unification, then return the output `Ty`
built from those indices via `@[reducible]` Ty constructors and
`Ty.subst0`.  No `Eq.mpr`, no `HEq.cast`, no propext leakage.  Each
`<name>_matches_Term_<ctor>` theorem witnesses that the extracted
output type agrees with the legacy `Term.<ctor>` constructor's own
output type *definitionally* (rfl-bodied).

## What's not yet in scope

* Closed-type ctors (boolElim / natElim / listElim / ...).  These
  need an explicit motive-type argument; the extractor signature
  differs from the Π/Σ pattern.  Future P2.2 follow-ups.
* HOTT ctors (idJ / oeqJ / idStrictRec).  Similar motive-driven
  pattern; future follow-ups.
* Cubical / modal / type-code / record / codata / session / effect
  ctors.  Each has its own family signature; future follow-ups.
* The opaque-children case (where typed indices are erased into a
  `Vector ChildEntry (arity g)` envelope).  Deferred to the well-
  typed-witness scheme documented in `Generator.lean`'s trailing
  comment block.

## Verification

All 12 declarations (6 extractors + 6 matching `rfl` theorems) are
`#assert_no_axioms` clean; see `Smoke/AuditGenerator.lean`. -/

namespace LeanFX2.Foundation.Polygraph

open LeanFX2

/-! ### Non-dependent function application -/

/-- **Output type for `gen_app`**.  The non-dependent function
application produces the codomain `B` of the arrow type `Ty.arrow A
B` pinned by the function child.  Lean's implicit unifier extracts
`A` and `B` from the function child's type index; the argument
child's type confirms `A`.  Output is `B` directly — no
substitution, since arrow is non-dependent. -/
def Generator.outputTypeApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Ty level scope :=
  let _functionWitness := functionTerm
  let _argumentWitness := argumentTerm
  codomainType

/-- Definitional match against `Term.app`'s legacy output type.
`Term.app functionTerm argumentTerm` has type
`Term context codomainType (RawTerm.app functionRaw argumentRaw)`.
This theorem witnesses that `outputTypeApp` extracts exactly
`codomainType` cast-free. -/
theorem Generator.outputTypeApp_matches_Term_app
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Generator.outputTypeApp functionTerm argumentTerm = codomainType := rfl

/-! ### Non-dependent function intro (arrow) -/

/-- **Output type for `gen_lam`**.  The non-dependent lambda
produces `Ty.arrow domainType codomainType`.  Lean's implicit
unifier extracts `domainType` from the extended context (the
`Ctx.cons _ domainType` binding) and `codomainType` from the
body's type index (`codomainType.weaken`).  Output is built directly
from those indices via `Ty.arrow`. -/
def Generator.outputTypeLam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body :
      Term (Ctx.cons context domainType) codomainType.weaken bodyRaw) :
    Ty level scope :=
  let _bodyWitness := body
  Ty.arrow domainType codomainType

/-- Definitional match against `Term.lam`'s legacy output type.
`Term.lam body` has type `Term context (Ty.arrow domainType
codomainType) (RawTerm.lam bodyRaw)`.  This theorem witnesses that
`outputTypeLam` extracts exactly `Ty.arrow domainType codomainType`
cast-free. -/
theorem Generator.outputTypeLam_matches_Term_lam
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body :
      Term (Ctx.cons context domainType) codomainType.weaken bodyRaw) :
    Generator.outputTypeLam body = Ty.arrow domainType codomainType := rfl

/-! ### Dependent function intro (Π) -/

/-- **Output type for `gen_lamPi`**.  The dependent Π lambda
produces `Ty.piTy domainType codomainType`.  The body's type index
is `codomainType` itself (at `scope + 1`, not weakened), so Lean's
unifier extracts both `domainType` and `codomainType` directly. -/
def Generator.outputTypeLamPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons context domainType) codomainType bodyRaw) :
    Ty level scope :=
  let _bodyWitness := body
  Ty.piTy domainType codomainType

/-- Definitional match against `Term.lamPi`'s legacy output type.
`Term.lamPi body` has type `Term context (Ty.piTy domainType
codomainType) (RawTerm.lam bodyRaw)`. -/
theorem Generator.outputTypeLamPi_matches_Term_lamPi
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons context domainType) codomainType bodyRaw) :
    Generator.outputTypeLamPi body = Ty.piTy domainType codomainType := rfl

/-! ### Σ pair intro -/

/-- **Output type for `gen_pair`**.  The Σ pair produces
`Ty.sigmaTy firstType secondType`.  The first value's type pins
`firstType`; the second value's type pins
`secondType.subst0 firstType firstRaw`, from which `secondType` is
recovered via Lean's higher-order unification (the substitution
shape is `@[reducible]`). -/
def Generator.outputTypePair {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Ty level scope :=
  let _firstWitness := firstValue
  let _secondWitness := secondValue
  Ty.sigmaTy firstType secondType

/-- Definitional match against `Term.pair`'s legacy output type.
`Term.pair firstValue secondValue` has type
`Term context (Ty.sigmaTy firstType secondType) (RawTerm.pair
firstRaw secondRaw)`. -/
theorem Generator.outputTypePair_matches_Term_pair
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Generator.outputTypePair firstValue secondValue =
      Ty.sigmaTy firstType secondType := rfl

/-! ### Σ pair first projection -/

/-- **Output type for `gen_fst`**.  The first projection of a
`Ty.sigmaTy firstType secondType` pair returns `firstType` directly. -/
def Generator.outputTypeFst {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Ty level scope :=
  let _pairWitness := pairTerm
  firstType

/-- Definitional match against `Term.fst`'s legacy output type.
`Term.fst pairTerm` has type `Term context firstType (RawTerm.fst
pairRaw)`. -/
theorem Generator.outputTypeFst_matches_Term_fst
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Generator.outputTypeFst pairTerm = firstType := rfl

/-! ### Σ pair second projection (dependent) -/

/-- **Output type for `gen_snd`**.  The second projection of a
`Ty.sigmaTy firstType secondType` pair returns
`secondType.subst0 firstType (RawTerm.fst pairRaw)` — the second
type substituted with the raw form of the first projection (so the
caller gets a `Ty` that depends on the actual pair's first
component).

This is the second dependent-output case in the Π/Σ family
(`appPi` was the first); it demonstrates that even when the output
type involves a `RawTerm` operation (`.fst pairRaw`) on a child's
raw payload, the extractor is `rfl`-verifiable. -/
def Generator.outputTypeSnd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Ty level scope :=
  let _pairWitness := pairTerm
  secondType.subst0 firstType (RawTerm.fst pairRaw)

/-- Definitional match against `Term.snd`'s legacy output type.
`Term.snd pairTerm` has type `Term context (secondType.subst0
firstType (RawTerm.fst pairRaw)) (RawTerm.snd pairRaw)`. -/
theorem Generator.outputTypeSnd_matches_Term_snd
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Generator.outputTypeSnd pairTerm =
      secondType.subst0 firstType (RawTerm.fst pairRaw) := rfl

/-! ### Bool eliminator (dependent motive) -/

/-- **Output type for `gen_boolElim`**.  The dependent bool
eliminator has motive `Ty level (scope + 1)`.  The output type
`motiveType.subst0 Ty.bool scrutineeRaw` substitutes the
scrutinee's raw form into the motive — the SAME substitution
pattern that `outputTypeAppPi` and `outputTypeSnd` exhibit, just
applied to a different family.

Lean's higher-order unifier pulls `motiveType` from EITHER branch
(the then-branch has type `motiveType.subst0 Ty.bool RawTerm.boolTrue`;
the else-branch has type `motiveType.subst0 Ty.bool RawTerm.boolFalse`);
the unification problem is `?motive.subst0 Ty.bool <known> = <given>`,
which Lean solves when `Ty.subst0` is `@[reducible]` and the given
type structure exposes the substitution shape. -/
def Generator.outputTypeBoolElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Ty level scope :=
  let _scrutineeWitness := scrutinee
  let _thenWitness := thenBranch
  let _elseWitness := elseBranch
  motiveType.subst0 Ty.bool scrutineeRaw

/-- Definitional match against `Term.boolElim`'s legacy output type.
`Term.boolElim scrutinee thenBranch elseBranch` has type
`Term context (motiveType.subst0 Ty.bool scrutineeRaw) (RawTerm.boolElim
scrutineeRaw thenRaw elseRaw)`. -/
theorem Generator.outputTypeBoolElim_matches_Term_boolElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Generator.outputTypeBoolElim scrutinee thenBranch elseBranch =
      motiveType.subst0 Ty.bool scrutineeRaw := rfl

/-! ### Nat eliminator (non-dependent) -/

/-- **Output type for `gen_natElim`**.  The non-dependent nat
eliminator has motive `Ty level scope`; output is the motive
itself.  Lean's unifier pins `motiveType` directly from the
zero-branch's type index (no substitution). -/
def Generator.outputTypeNatElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Ty level scope :=
  let _scrutineeWitness := scrutinee
  let _zeroWitness := zeroBranch
  let _succWitness := succBranch
  motiveType

/-- Definitional match against `Term.natElim`'s legacy output type. -/
theorem Generator.outputTypeNatElim_matches_Term_natElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Generator.outputTypeNatElim scrutinee zeroBranch succBranch =
      motiveType := rfl

/-! ### Nat recursor (non-dependent) -/

/-- **Output type for `gen_natRec`**.  Same shape as `natElim` but
with succ-branch type `Ty.arrow Ty.nat (Ty.arrow motiveType
motiveType)` — the recursor passes both the predecessor and the
accumulated result.  Output is still just the motive. -/
def Generator.outputTypeNatRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context
        (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    Ty level scope :=
  let _scrutineeWitness := scrutinee
  let _zeroWitness := zeroBranch
  let _succWitness := succBranch
  motiveType

/-- Definitional match against `Term.natRec`'s legacy output type. -/
theorem Generator.outputTypeNatRec_matches_Term_natRec
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context
        (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    Generator.outputTypeNatRec scrutinee zeroBranch succBranch =
      motiveType := rfl

/-! ### List eliminator (non-dependent) -/

/-- **Output type for `gen_listElim`**.  Non-dependent list
eliminator: motive is `Ty level scope`; output is the motive
itself.  Both `elementType` (from the scrutinee) and `motiveType`
(from the nil-branch) are pinned by Lean's unifier. -/
def Generator.outputTypeListElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    Ty level scope :=
  let _scrutineeWitness := scrutinee
  let _nilWitness := nilBranch
  let _consWitness := consBranch
  motiveType

/-- Definitional match against `Term.listElim`'s legacy output type. -/
theorem Generator.outputTypeListElim_matches_Term_listElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    Generator.outputTypeListElim scrutinee nilBranch consBranch =
      motiveType := rfl

/-! ### Option matcher (non-dependent) -/

/-- **Output type for `gen_optionMatch`**.  Non-dependent option
matcher: motive `Ty level scope`; output is the motive. -/
def Generator.outputTypeOptionMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch :
      Term context (Ty.arrow elementType motiveType) someRaw) :
    Ty level scope :=
  let _scrutineeWitness := scrutinee
  let _noneWitness := noneBranch
  let _someWitness := someBranch
  motiveType

/-- Definitional match against `Term.optionMatch`'s legacy output type. -/
theorem Generator.outputTypeOptionMatch_matches_Term_optionMatch
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch :
      Term context (Ty.arrow elementType motiveType) someRaw) :
    Generator.outputTypeOptionMatch scrutinee noneBranch someBranch =
      motiveType := rfl

/-! ### Either matcher (non-dependent) -/

/-- **Output type for `gen_eitherMatch`**.  Non-dependent either
matcher: motive `Ty level scope`; output is the motive.  Pulls
`leftType`, `rightType`, and `motiveType` via implicit
unification from the scrutinee and the two branches. -/
def Generator.outputTypeEitherMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch :
      Term context (Ty.arrow leftType motiveType) leftBranchRaw)
    (rightBranch :
      Term context (Ty.arrow rightType motiveType) rightBranchRaw) :
    Ty level scope :=
  let _scrutineeWitness := scrutinee
  let _leftWitness := leftBranch
  let _rightWitness := rightBranch
  motiveType

/-- Definitional match against `Term.eitherMatch`'s legacy output type. -/
theorem Generator.outputTypeEitherMatch_matches_Term_eitherMatch
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch :
      Term context (Ty.arrow leftType motiveType) leftBranchRaw)
    (rightBranch :
      Term context (Ty.arrow rightType motiveType) rightBranchRaw) :
    Generator.outputTypeEitherMatch scrutinee leftBranch rightBranch =
      motiveType := rfl

/-! ### HoTT identity types — refl + J + equivApp -/

/-- **Output type for `gen_refl`**.  The reflexivity proof of HoTT
identity at carrier `T` and witness `w` has type
`Ty.id T w w` — both endpoints are the same witness.  Unlike most
extractors in this file, `gen_refl`'s "children" are the explicit
type/witness parameters (no typed child needed: refl is constructor-
nullary at the RawTerm level beyond carrying its witness).

The extractor takes the carrier and the raw witness directly. -/
def Generator.outputTypeRefl {mode : Mode} {level scope : Nat}
    (_context : Ctx mode level scope)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Ty level scope :=
  Ty.id carrier rawWitness rawWitness

/-- Definitional match against `Term.refl`'s legacy output type.
`Term.refl carrier rawWitness` has type `Term context (Ty.id carrier
rawWitness rawWitness) (RawTerm.refl rawWitness)`. -/
theorem Generator.outputTypeRefl_matches_Term_refl
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Generator.outputTypeRefl context carrier rawWitness =
      Ty.id carrier rawWitness rawWitness := rfl

/-- **Output type for `gen_idJ`**.  The HoTT J eliminator with
non-dependent motive `Ty level scope` returns the motive directly.
Lean's unifier pulls `motiveType` from the base-case's type index;
`carrier`, `leftEndpoint`, `rightEndpoint` come from the witness's
`Ty.id` index. -/
def Generator.outputTypeIdJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    Ty level scope :=
  let _baseWitness := baseCase
  let _witnessWitness := witness
  motiveType

/-- Definitional match against `Term.idJ`'s legacy output type. -/
theorem Generator.outputTypeIdJ_matches_Term_idJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    Generator.outputTypeIdJ baseCase witness = motiveType := rfl

/-! ### Observational equality — oeqRefl + oeqJ -/

/-- **Output type for `gen_oeqRefl`**.  Observational-equality
reflexivity at carrier `T` and witness `w`; output is
`Ty.oeq T w w`. -/
def Generator.outputTypeOeqRefl {mode : Mode} {level scope : Nat}
    (_context : Ctx mode level scope)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Ty level scope :=
  Ty.oeq carrier rawWitness rawWitness

/-- Definitional match against `Term.oeqRefl`'s legacy output type. -/
theorem Generator.outputTypeOeqRefl_matches_Term_oeqRefl
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Generator.outputTypeOeqRefl context carrier rawWitness =
      Ty.oeq carrier rawWitness rawWitness := rfl

/-- **Output type for `gen_oeqJ`**.  The observational-J eliminator
with non-dependent motive returns the motive.  Mirrors `outputTypeIdJ`
but at `Ty.oeq` instead of `Ty.id`. -/
def Generator.outputTypeOeqJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw) :
    Ty level scope :=
  let _baseWitness := baseCase
  let _witnessWitness := witness
  motiveType

/-- Definitional match against `Term.oeqJ`'s legacy output type. -/
theorem Generator.outputTypeOeqJ_matches_Term_oeqJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw) :
    Generator.outputTypeOeqJ baseCase witness = motiveType := rfl

/-! ### Strict identity types — idStrictRefl + idStrictRec -/

/-- **Output type for `gen_idStrictRefl`**.  Strict-identity reflexivity
at carrier `T` and witness `w`; output is `Ty.idStrict T w w`.  The
strict-mode constraint `mode = Mode.strict` is carried as a propositional
input mirroring `Term.idStrictRefl`'s signature. -/
def Generator.outputTypeIdStrictRefl {mode : Mode} {level scope : Nat}
    (_context : Ctx mode level scope)
    (_modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Ty level scope :=
  Ty.idStrict carrier rawWitness rawWitness

/-- Definitional match against `Term.idStrictRefl`'s legacy output type. -/
theorem Generator.outputTypeIdStrictRefl_matches_Term_idStrictRefl
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    Generator.outputTypeIdStrictRefl context modeIsStrict carrier rawWitness =
      Ty.idStrict carrier rawWitness rawWitness := rfl

/-- **Output type for `gen_idStrictRec`**.  Strict-identity recursor
with non-dependent motive returns the motive.  Mirrors `outputTypeIdJ`
but at `Ty.idStrict` and carrying the strict-mode constraint. -/
def Generator.outputTypeIdStrictRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (_modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw) :
    Ty level scope :=
  let _baseWitness := baseCase
  let _witnessWitness := witness
  motiveType

/-- Definitional match against `Term.idStrictRec`'s legacy output type. -/
theorem Generator.outputTypeIdStrictRec_matches_Term_idStrictRec
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw) :
    Generator.outputTypeIdStrictRec modeIsStrict baseCase witness =
      motiveType := rfl

/-! ### Type equivalence application -/

/-- **Output type for `gen_equivApp`**.  Apply a packaged equivalence
`Ty.equiv carrierA carrierB` to an argument of `carrierA`; output is
`carrierB`.  Both carriers come from the equivalence's `Ty.equiv`
index; the argument confirms `carrierA`. -/
def Generator.outputTypeEquivApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm :
      Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw) :
    Ty level scope :=
  let _equivWitness := equivTerm
  let _argumentWitness := argumentTerm
  carrierB

/-- Definitional match against `Term.equivApp`'s legacy output type.
`Term.equivApp equivTerm argumentTerm` has type `Term context
carrierB (RawTerm.equivApp equivRaw argumentRaw)`. -/
theorem Generator.outputTypeEquivApp_matches_Term_equivApp
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm :
      Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw) :
    Generator.outputTypeEquivApp equivTerm argumentTerm = carrierB := rfl

/-! ### Modal family (`modIntro` / `modElim` / `subsume`)

Layer 1 ships RAW-SIDE SCAFFOLDING ONLY (see comment block at
`Term.lean:295-300`): the Phase 1 modal trio preserves `innerType`
without applying any `Ty.modal` wrapper.  When Layer 6 lands the
real modality 1-cells, these three extractors will be refactored to
take a `Modality` + produce `Ty.modal modality innerType`.  Today,
they ship as identity extractors. -/

/-- `Term.modIntro`'s output is its inner term's type (Phase 1
scaffolding). -/
def Generator.outputTypeModIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Ty level scope :=
  let _witness := innerTerm
  innerType

/-- Definitional match against `Term.modIntro`'s output type. -/
theorem Generator.outputTypeModIntro_matches_Term_modIntro
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Generator.outputTypeModIntro innerTerm = innerType := rfl

/-- `Term.modElim`'s output is its inner term's type (Phase 1
scaffolding). -/
def Generator.outputTypeModElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Ty level scope :=
  let _witness := innerTerm
  innerType

/-- Definitional match against `Term.modElim`'s output type. -/
theorem Generator.outputTypeModElim_matches_Term_modElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Generator.outputTypeModElim innerTerm = innerType := rfl

/-- `Term.subsume`'s output is its inner term's type (Phase 1
scaffolding). -/
def Generator.outputTypeSubsume {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Ty level scope :=
  let _witness := innerTerm
  innerType

/-- Definitional match against `Term.subsume`'s output type. -/
theorem Generator.outputTypeSubsume_matches_Term_subsume
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Generator.outputTypeSubsume innerTerm = innerType := rfl

/-! ### Cubical interval family

Five extractors mirroring `Term.interval0`, `Term.interval1`,
`Term.intervalOpp`, `Term.intervalMeet`, `Term.intervalJoin` (see
`Term.lean:314-336`).  All five return `Ty.interval` regardless of
children — interval0/interval1 are arity-0 nullaries; intervalOpp
is unary; intervalMeet/intervalJoin are binary.  The output is
constant across children because `Ty.interval` carries no
parameters beyond `level`/`scope` (universe-agnostic). -/

/-- `Term.interval0`'s output is `Ty.interval`. -/
def Generator.outputTypeInterval0 (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Ty level scope :=
  let _witness := context
  Ty.interval

/-- Definitional match against `Term.interval0`'s output type. -/
theorem Generator.outputTypeInterval0_matches_Term_interval0
    (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Generator.outputTypeInterval0 mode level scope context =
      (Ty.interval : Ty level scope) := rfl

/-- `Term.interval1`'s output is `Ty.interval`. -/
def Generator.outputTypeInterval1 (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Ty level scope :=
  let _witness := context
  Ty.interval

/-- Definitional match against `Term.interval1`'s output type. -/
theorem Generator.outputTypeInterval1_matches_Term_interval1
    (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Generator.outputTypeInterval1 mode level scope context =
      (Ty.interval : Ty level scope) := rfl

/-- `Term.intervalOpp`'s output is `Ty.interval`. -/
def Generator.outputTypeIntervalOpp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw) :
    Ty level scope :=
  let _witness := innerValue
  Ty.interval

/-- Definitional match against `Term.intervalOpp`'s output type. -/
theorem Generator.outputTypeIntervalOpp_matches_Term_intervalOpp
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw) :
    Generator.outputTypeIntervalOpp innerValue =
      (Ty.interval : Ty level scope) := rfl

/-- `Term.intervalMeet`'s output is `Ty.interval`. -/
def Generator.outputTypeIntervalMeet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw) :
    Ty level scope :=
  let _leftWitness := leftValue
  let _rightWitness := rightValue
  Ty.interval

/-- Definitional match against `Term.intervalMeet`'s output type. -/
theorem Generator.outputTypeIntervalMeet_matches_Term_intervalMeet
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw) :
    Generator.outputTypeIntervalMeet leftValue rightValue =
      (Ty.interval : Ty level scope) := rfl

/-- `Term.intervalJoin`'s output is `Ty.interval`. -/
def Generator.outputTypeIntervalJoin {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw) :
    Ty level scope :=
  let _leftWitness := leftValue
  let _rightWitness := rightValue
  Ty.interval

/-- Definitional match against `Term.intervalJoin`'s output type. -/
theorem Generator.outputTypeIntervalJoin_matches_Term_intervalJoin
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw) :
    Generator.outputTypeIntervalJoin leftValue rightValue =
      (Ty.interval : Ty level scope) := rfl

/-! ### Record family (`recordIntro` / `recordProj`)

Mirrors `Term.lean:483-497`.  Single-field records — multi-field
surface records elaborate to nested single-field records.

* `recordIntro` wraps its child's type in `Ty.record`.
* `recordProj` projects out the wrapped type. -/

/-- `Term.recordIntro`'s output wraps the field type in `Ty.record`. -/
def Generator.outputTypeRecordIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw) :
    Ty level scope :=
  let _witness := firstField
  Ty.record singleFieldType

/-- Definitional match against `Term.recordIntro`'s output type. -/
theorem Generator.outputTypeRecordIntro_matches_Term_recordIntro
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw) :
    Generator.outputTypeRecordIntro firstField =
      Ty.record singleFieldType := rfl

/-- `Term.recordProj`'s output is the field type carried by the
record value. -/
def Generator.outputTypeRecordProj {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw) :
    Ty level scope :=
  let _witness := recordValue
  singleFieldType

/-- Definitional match against `Term.recordProj`'s output type. -/
theorem Generator.outputTypeRecordProj_matches_Term_recordProj
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw) :
    Generator.outputTypeRecordProj recordValue = singleFieldType := rfl

/-! ### Refinement family (`refineIntro` / `refineElim`)

Mirrors `Term.lean:498-518`.  `refineIntro` packages a base value with
a unit-typed proof certificate; `refineElim` forgets the proof. -/

/-- `Term.refineIntro`'s output is `Ty.refine baseType predicate`. -/
def Generator.outputTypeRefineIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw) :
    Ty level scope :=
  let _valueWitness := baseValue
  let _proofWitness := predicateProof
  Ty.refine baseType predicate

/-- Definitional match against `Term.refineIntro`'s output type. -/
theorem Generator.outputTypeRefineIntro_matches_Term_refineIntro
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw) :
    Generator.outputTypeRefineIntro predicate baseValue predicateProof =
      Ty.refine baseType predicate := rfl

/-- `Term.refineElim`'s output is the base type of the refinement. -/
def Generator.outputTypeRefineElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw) :
    Ty level scope :=
  let _witness := refinedValue
  baseType

/-- Definitional match against `Term.refineElim`'s output type. -/
theorem Generator.outputTypeRefineElim_matches_Term_refineElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw) :
    Generator.outputTypeRefineElim refinedValue = baseType := rfl

/-! ### Codata family (`codataUnfold` / `codataDest`)

Mirrors `Term.lean:519-537`.  `codataUnfold` packages a state +
transition into a `Ty.codata`; `codataDest` observes one output. -/

/-- `Term.codataUnfold`'s output is `Ty.codata stateType outputType`. -/
def Generator.outputTypeCodataUnfold {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw) :
    Ty level scope :=
  let _stateWitness := initialState
  let _transitionWitness := transition
  Ty.codata stateType outputType

/-- Definitional match against `Term.codataUnfold`'s output type. -/
theorem Generator.outputTypeCodataUnfold_matches_Term_codataUnfold
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw) :
    Generator.outputTypeCodataUnfold initialState transition =
      Ty.codata stateType outputType := rfl

/-- `Term.codataDest`'s output is the codata's output type. -/
def Generator.outputTypeCodataDest {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw) :
    Ty level scope :=
  let _witness := codataValue
  outputType

/-- Definitional match against `Term.codataDest`'s output type. -/
theorem Generator.outputTypeCodataDest_matches_Term_codataDest
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw) :
    Generator.outputTypeCodataDest codataValue = outputType := rfl

/-! ### Session family (`sessionSend` / `sessionRecv`)

Mirrors `Term.lean:538-558`.  Both preserve the session carrier — the
typed core currently records `Ty.session protocolStep` and exposes
congruence parity; protocol-state advancement is the Sessions layer's
job. -/

/-- `Term.sessionSend`'s output preserves `Ty.session protocolStep`. -/
def Generator.outputTypeSessionSend {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw) :
    Ty level scope :=
  let _channelWitness := channel
  let _payloadWitness := payload
  Ty.session protocolStep

/-- Definitional match against `Term.sessionSend`'s output type. -/
theorem Generator.outputTypeSessionSend_matches_Term_sessionSend
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw) :
    Generator.outputTypeSessionSend protocolStep channel payload =
      Ty.session protocolStep := rfl

/-- `Term.sessionRecv`'s output preserves `Ty.session protocolStep`. -/
def Generator.outputTypeSessionRecv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw) :
    Ty level scope :=
  let _witness := channel
  Ty.session protocolStep

/-- Definitional match against `Term.sessionRecv`'s output type. -/
theorem Generator.outputTypeSessionRecv_matches_Term_sessionRecv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw) :
    Generator.outputTypeSessionRecv channel =
      Ty.session protocolStep := rfl

/-! ### Effect family (`effectPerform`)

Mirrors `Term.lean:559-582`.  `effectPerform` carries an
`Effects.EffectRow`, an `Effects.OperationSignature`, and a
`CanPerform` evidence witness; the result type is `Ty.effect
operationSignature.resultCarrier effectTag`. -/

/-- `Term.effectPerform`'s output is
`Ty.effect operationSignature.resultCarrier effectTag`. -/
def Generator.outputTypeEffectPerform {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw) :
    Ty level scope :=
  let _effectRowWitness := effectRow
  let _canPerformWitness := canPerformOperation
  let _operationWitness := operationTag
  let _argumentsWitness := arguments
  Ty.effect operationSignature.resultCarrier effectTag

/-- Definitional match against `Term.effectPerform`'s output type. -/
theorem Generator.outputTypeEffectPerform_matches_Term_effectPerform
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw) :
    Generator.outputTypeEffectPerform effectTag effectRow
        operationSignature canPerformOperation operationTag arguments =
      Ty.effect operationSignature.resultCarrier effectTag := rfl

/-! ### Variable lookup (`var`)

Mirrors `Term.lean:97-99`.  The output type is `varType context
position` — context-and-position-dependent.  Unlike every previous
extractor in this file, the output depends on a non-Ty index, so
the extractor takes `position` explicitly. -/

/-- `Term.var`'s output is `varType context position` (the type
recorded at the given de Bruijn position). -/
def Generator.outputTypeVar {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (position : Fin scope) :
    Ty level scope :=
  varType context position

/-- Definitional match against `Term.var`'s output type. -/
theorem Generator.outputTypeVar_matches_Term_var
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (position : Fin scope) :
    Generator.outputTypeVar context position =
      varType context position := rfl

/-! ### Unit (`unit`)

Mirrors `Term.lean:101-102`.  Nullary, returns `Ty.unit`. -/

/-- `Term.unit`'s output is `Ty.unit`. -/
def Generator.outputTypeUnit (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Ty level scope :=
  let _witness := context
  Ty.unit

/-- Definitional match against `Term.unit`'s output type. -/
theorem Generator.outputTypeUnit_matches_Term_unit
    (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Generator.outputTypeUnit mode level scope context =
      (Ty.unit : Ty level scope) := rfl

/-! ### Booleans (`boolTrue` / `boolFalse`)

Mirrors `Term.lean:148-151`.  Nullary, both return `Ty.bool`. -/

/-- `Term.boolTrue`'s output is `Ty.bool`. -/
def Generator.outputTypeBoolTrue (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Ty level scope :=
  let _witness := context
  Ty.bool

/-- Definitional match against `Term.boolTrue`'s output type. -/
theorem Generator.outputTypeBoolTrue_matches_Term_boolTrue
    (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Generator.outputTypeBoolTrue mode level scope context =
      (Ty.bool : Ty level scope) := rfl

/-- `Term.boolFalse`'s output is `Ty.bool`. -/
def Generator.outputTypeBoolFalse (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Ty level scope :=
  let _witness := context
  Ty.bool

/-- Definitional match against `Term.boolFalse`'s output type. -/
theorem Generator.outputTypeBoolFalse_matches_Term_boolFalse
    (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Generator.outputTypeBoolFalse mode level scope context =
      (Ty.bool : Ty level scope) := rfl

/-! ### Naturals (`natZero` / `natSucc`)

Mirrors `Term.lean:163-168`.  `natZero` is nullary; `natSucc` is
unary on `Ty.nat`.  Both return `Ty.nat`. -/

/-- `Term.natZero`'s output is `Ty.nat`. -/
def Generator.outputTypeNatZero (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Ty level scope :=
  let _witness := context
  Ty.nat

/-- Definitional match against `Term.natZero`'s output type. -/
theorem Generator.outputTypeNatZero_matches_Term_natZero
    (mode : Mode) (level scope : Nat)
    (context : Ctx mode level scope) :
    Generator.outputTypeNatZero mode level scope context =
      (Ty.nat : Ty level scope) := rfl

/-- `Term.natSucc`'s output is `Ty.nat`. -/
def Generator.outputTypeNatSucc {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw) :
    Ty level scope :=
  let _witness := predecessor
  Ty.nat

/-- Definitional match against `Term.natSucc`'s output type. -/
theorem Generator.outputTypeNatSucc_matches_Term_natSucc
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw) :
    Generator.outputTypeNatSucc predecessor =
      (Ty.nat : Ty level scope) := rfl

/-! ### Lists (`listNil` / `listCons`)

Mirrors `Term.lean:184-192`.  Both produce `Ty.listType elementType`.
`listNil` is nullary in raw-term arity; the element type is supplied
as an explicit parameter so the extractor's output type is fully
determined (the corresponding typed Term ctor takes `elementType` as
an implicit, but here we cannot infer it without a child to pin
it). -/

/-- `Term.listNil`'s output is `Ty.listType elementType`. -/
def Generator.outputTypeListNil {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (elementType : Ty level scope) :
    Ty level scope :=
  let _witness := context
  Ty.listType elementType

/-- Definitional match against `Term.listNil`'s output type. -/
theorem Generator.outputTypeListNil_matches_Term_listNil
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (elementType : Ty level scope) :
    Generator.outputTypeListNil context elementType =
      Ty.listType elementType := rfl

/-- `Term.listCons`'s output is `Ty.listType elementType`. -/
def Generator.outputTypeListCons {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw) :
    Ty level scope :=
  let _headWitness := headTerm
  let _tailWitness := tailTerm
  Ty.listType elementType

/-- Definitional match against `Term.listCons`'s output type. -/
theorem Generator.outputTypeListCons_matches_Term_listCons
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw) :
    Generator.outputTypeListCons headTerm tailTerm =
      Ty.listType elementType := rfl

/-! ### Options (`optionNone` / `optionSome`)

Mirrors `Term.lean:202-209`.  Both produce `Ty.optionType
elementType`.  Same nullary-needs-explicit-element story as
`listNil`. -/

/-- `Term.optionNone`'s output is `Ty.optionType elementType`. -/
def Generator.outputTypeOptionNone {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (elementType : Ty level scope) :
    Ty level scope :=
  let _witness := context
  Ty.optionType elementType

/-- Definitional match against `Term.optionNone`'s output type. -/
theorem Generator.outputTypeOptionNone_matches_Term_optionNone
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (elementType : Ty level scope) :
    Generator.outputTypeOptionNone context elementType =
      Ty.optionType elementType := rfl

/-- `Term.optionSome`'s output is `Ty.optionType elementType`. -/
def Generator.outputTypeOptionSome {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw) :
    Ty level scope :=
  let _witness := valueTerm
  Ty.optionType elementType

/-- Definitional match against `Term.optionSome`'s output type. -/
theorem Generator.outputTypeOptionSome_matches_Term_optionSome
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw) :
    Generator.outputTypeOptionSome valueTerm =
      Ty.optionType elementType := rfl

/-! ### Eithers (`eitherInl` / `eitherInr`)

Mirrors `Term.lean:218-227`.  Both produce `Ty.eitherType leftType
rightType`.  Each is unary in raw-term arity but the OTHER side's
type is implicit-yet-needed in the output, so we expose both as
extractor parameters. -/

/-- `Term.eitherInl`'s output is `Ty.eitherType leftType rightType`. -/
def Generator.outputTypeEitherInl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType : Ty level scope}
    (rightType : Ty level scope)
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw) :
    Ty level scope :=
  let _witness := valueTerm
  Ty.eitherType leftType rightType

/-- Definitional match against `Term.eitherInl`'s output type. -/
theorem Generator.outputTypeEitherInl_matches_Term_eitherInl
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType : Ty level scope}
    (rightType : Ty level scope)
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw) :
    Generator.outputTypeEitherInl rightType valueTerm =
      Ty.eitherType leftType rightType := rfl

/-- `Term.eitherInr`'s output is `Ty.eitherType leftType rightType`. -/
def Generator.outputTypeEitherInr {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (leftType : Ty level scope)
    {rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw) :
    Ty level scope :=
  let _witness := valueTerm
  Ty.eitherType leftType rightType

/-- Definitional match against `Term.eitherInr`'s output type. -/
theorem Generator.outputTypeEitherInr_matches_Term_eitherInr
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (leftType : Ty level scope)
    {rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw) :
    Generator.outputTypeEitherInr leftType valueTerm =
      Ty.eitherType leftType rightType := rfl

/-! ### Type-code family (11 ctors, CUMUL-2.4)

Mirrors `Term.lean:583-1028` (`universeCode`, `arrowCode`, `piTyCode`,
`sigmaTyCode`, `productCode`, `sumCode`, `listCode`, `optionCode`,
`eitherCode`, `idCode`, `equivCode`).

These are VALUE-shaped (schematic raw) per CUMUL-2.4 discipline —
the raw payload carries the to-be-decoded type structure, but no
typed-child obligations.  Every extractor follows the uniform shape:

* takes `outerLevel : UniverseLevel` + `levelLe : outerLevel.toNat
  + 1 ≤ level` + the raw-payload arguments,
* returns `Ty.universe outerLevel levelLe`.

The uniformity is the whole point — each type code packages its
syntactic shape inside the raw payload, while the typed Term layer
just records "this is a type code inhabiting `Ty.universe N`". -/

/-- `Term.universeCode`'s output is `Ty.universe outerLevel levelLe`.
The inner level + cumulativity witness are recorded on the raw side. -/
def Generator.outputTypeUniverseCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Ty level scope :=
  let _contextWitness := context
  let _innerWitness := innerLevel
  let _cumulWitness := cumulOk
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.universeCode`'s output type. -/
theorem Generator.outputTypeUniverseCode_matches_Term_universeCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Generator.outputTypeUniverseCode context innerLevel outerLevel
        cumulOk levelLe =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.arrowCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeArrowCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _domainWitness := domainCodeRaw
  let _codomainWitness := codomainCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.arrowCode`'s output type. -/
theorem Generator.outputTypeArrowCode_matches_Term_arrowCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    Generator.outputTypeArrowCode context outerLevel levelLe
        domainCodeRaw codomainCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.piTyCode`'s output is `Ty.universe outerLevel levelLe`.
Codomain raw lives at `scope + 1` (Π binder). -/
def Generator.outputTypePiTyCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    Ty level scope :=
  let _contextWitness := context
  let _domainWitness := domainCodeRaw
  let _codomainWitness := codomainCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.piTyCode`'s output type. -/
theorem Generator.outputTypePiTyCode_matches_Term_piTyCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    Generator.outputTypePiTyCode context outerLevel levelLe
        domainCodeRaw codomainCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.sigmaTyCode`'s output is `Ty.universe outerLevel levelLe`.
Codomain raw lives at `scope + 1` (Σ binder). -/
def Generator.outputTypeSigmaTyCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    Ty level scope :=
  let _contextWitness := context
  let _domainWitness := domainCodeRaw
  let _codomainWitness := codomainCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.sigmaTyCode`'s output type. -/
theorem Generator.outputTypeSigmaTyCode_matches_Term_sigmaTyCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    Generator.outputTypeSigmaTyCode context outerLevel levelLe
        domainCodeRaw codomainCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.productCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeProductCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _firstWitness := firstCodeRaw
  let _secondWitness := secondCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.productCode`'s output type. -/
theorem Generator.outputTypeProductCode_matches_Term_productCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    Generator.outputTypeProductCode context outerLevel levelLe
        firstCodeRaw secondCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.sumCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeSumCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _leftWitness := leftCodeRaw
  let _rightWitness := rightCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.sumCode`'s output type. -/
theorem Generator.outputTypeSumCode_matches_Term_sumCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    Generator.outputTypeSumCode context outerLevel levelLe
        leftCodeRaw rightCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.listCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeListCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _elementWitness := elementCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.listCode`'s output type. -/
theorem Generator.outputTypeListCode_matches_Term_listCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    Generator.outputTypeListCode context outerLevel levelLe
        elementCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.optionCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeOptionCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _elementWitness := elementCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.optionCode`'s output type. -/
theorem Generator.outputTypeOptionCode_matches_Term_optionCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    Generator.outputTypeOptionCode context outerLevel levelLe
        elementCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.eitherCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeEitherCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _leftWitness := leftCodeRaw
  let _rightWitness := rightCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.eitherCode`'s output type. -/
theorem Generator.outputTypeEitherCode_matches_Term_eitherCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    Generator.outputTypeEitherCode context outerLevel levelLe
        leftCodeRaw rightCodeRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.idCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeIdCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _typeCodeWitness := typeCodeRaw
  let _leftWitness := leftRaw
  let _rightWitness := rightRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.idCode`'s output type. -/
theorem Generator.outputTypeIdCode_matches_Term_idCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    Generator.outputTypeIdCode context outerLevel levelLe
        typeCodeRaw leftRaw rightRaw =
      Ty.universe outerLevel levelLe := rfl

/-- `Term.equivCode`'s output is `Ty.universe outerLevel levelLe`. -/
def Generator.outputTypeEquivCode {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    Ty level scope :=
  let _contextWitness := context
  let _leftWitness := leftTypeCodeRaw
  let _rightWitness := rightTypeCodeRaw
  Ty.universe outerLevel levelLe

/-- Definitional match against `Term.equivCode`'s output type. -/
theorem Generator.outputTypeEquivCode_matches_Term_equivCode
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    Generator.outputTypeEquivCode context outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw =
      Ty.universe outerLevel levelLe := rfl

end LeanFX2.Foundation.Polygraph

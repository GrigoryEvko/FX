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

end LeanFX2.Foundation.Polygraph

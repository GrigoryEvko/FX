import FX1Poly.Typed.HasType

/-! # FX1Poly/Typed/HasTypeGen — the cascade-free dependent-binary type-formation shape-arm

The mutual `HasTypeGen` + `DependentBinaryFormationChildren` inductive: a
typing judgment whose type-formation rules are per-SHAPE arms, each
generic over the `Generator` via a metadata predicate (NOT a
per-generator arm).

Four arms: `var`, `conv`, the nullary `universeFormation` shape-arm, and
ONE per-shape `dependentBinaryFormation` arm — the dependent-binary
type-formation shape, covering `gen_piTyCode` / `gen_sigmaTyCode` (any
generator the `isDependentBinaryFormer` whitelist admits reuses it with
zero new code).  These are two of the ~6 shape-arms Decision 4 calls for
(one arm per SHAPE, not a per-generator cascade and not one fully-generic
`TypingRule`-driven arm).

## Why the FIXED `[0, 1]` dependent-binary spine (not a fully-variadic spine)

The genuinely-hard, design-specific complication of a TYPING spine
(absent from the proven `StepChildren` precedent in `Core/Step.lean`)
is that a DEPENDENT former threads a PRIOR SIBLING into a later
sibling's context: the codomain child of `Pi domain. codomain` is typed
in the context EXTENDED BY THE DOMAIN child.  A fully-variadic spine
that only knew the `binderShifts` list could not, in general, know WHICH
prior child becomes the new binding type — that is per-shape data, not
recoverable from `binderShifts` alone.

For the `[0, 1]` dependent-binary shape the binding is exactly the head
(domain) child, so the spine is a SINGLE constructor
`dependentBinary` that takes BOTH children's typing premises at once
(the shape is a fixed two-element list `[0, 1]`, so no head-first
peeling is needed):

* `domainTyped`   — the shift-`0` domain child, typed at the parent scope.
* `codomainTyped` — the shift-`1` codomain child, typed in the parent
  context EXTENDED by the domain child, at scope `parentScope + 1`.

Its conclusion fixes the children to `RawTermChildren.binderShape
domainCode codomainCode`, whose index is definitionally `[0, 1]`.  So
the spine itself FORCES the parent generator's `binderShifts` to be
`[0, 1]` (the children index of the `dependentBinaryFormation` arm must
unify), independently of the `isDependentBinaryFormer` whitelist.

This keeps the arm GENERIC over the Generator (it fires for ANY
`generator` accepted by `isDependentBinaryFormer`; both whitelisted
generators happen to have `binderShifts = [0, 1]` and `payload = Unit`),
yet sidesteps the unknown-prior-sibling problem and matches the proven
`RawTerm` / `RawTermChildren` and `Step` / `StepChildren` mutual shapes
exactly.  Future non-`[0, 1]` shapes (flat eliminators, motive-carrying
dependent eliminators) get their OWN spine inductives / their own
shape-arms — still ~6 shapes, never 194, never 1 (polycell.md §11.8.5
Decision 4, P13).

## The mutual-index rule (the core zero-axiom trick)

`DependentBinaryFormationChildren`'s INDEX-FAMILY SIGNATURE references
ONLY `PolyProfile`, `Nat`, `LevelExpr`, `UniverseFlag`, `List Nat`,
`TypingContext`, `RawTerm`, and `RawTermChildren` — it NEVER names
`HasTypeGen`.  Lean's kernel type-checks each inductive header
(`check_inductive_types`) BEFORE declaring siblings, so a sibling name
in an index family is rejected.  `DependentBinaryFormationChildren`
references `HasTypeGen` ONLY POSITIVELY, inside the constructor PREMISES
(`dependentBinary`'s `domainTyped` / `codomainTyped` child-typing
hypotheses).  This mirrors `StepChildren` (`Core/Step.lean:562`), the
proven zero-axiom precedent.

## The output universe level is an EXPLICIT INDEX (no large elim)

The `dependentBinaryFormation` arm's output classifier is
`universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag`,
where `domainLevel` / `codomainLevel` are EXPLICIT arguments of the arm
threaded through the spine (NOT eliminated out of any proof-relevant
level data).  `HasTypeGen` stays `Prop`-valued: no elimination of level
information into `Type`.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (confirmed: all seven declarations report
"does not depend on any axioms").  The arm carries NO `Eq.mpr` / `▸`
casts: shape-soundness is enforced by (a) the `decide`-over-
`DecidableEq Generator` whitelist hypothesis `isDependentBinaryFormer
generator = true`, and (b) the spine constructor's children index
`RawTermChildren.binderShape …` (definitionally `[0, 1]`), which
unifies only when the parent generator's `binderShifts` is `[0, 1]`.
The smoke lemmas reconstruct Pi- and Sigma-formation by direct
constructor application.  Audit-gated alongside `HasType.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Metadata predicate selecting the dependent-binary type formers whose
typing rule is EXACTLY dependent-binary universe formation: `gen_piTyCode`
and `gen_sigmaTyCode` (matching `HasType`'s `piFormation` + `sigmaFormation`).
An EXPLICIT whitelist via `DecidableEq Generator`, NOT a `binderShifts ==
[0, 1]` structural proxy: `gen_polyFunctor` ALSO carries `binderShifts =
[0, 1]` (`GeneratorCore.lean:740`) yet is a polynomial functor — NOT a
universe inhabitant — so the proxy would derive a false typing and violate
0-FP soundness (P1).  Adding a further `[0, 1]` former is one `||` disjunct
here — one metadata row, never a new `HasTypeGen` arm (P13 cascade-freedom).
`decide`-over-`DecidableEq` is propext-free (no match-compiler wildcard over
the 194-constructor enum). -/
def isDependentBinaryFormer (generator : Generator) : Bool :=
  decide (generator = .gen_piTyCode) || decide (generator = .gen_sigmaTyCode)

/-- `gen_piTyCode` is a dependent-binary former (metadata check). -/
theorem isDependentBinaryFormer_piTyCode :
    isDependentBinaryFormer .gen_piTyCode = true := rfl

/-- `gen_sigmaTyCode` is a dependent-binary former (metadata check). -/
theorem isDependentBinaryFormer_sigmaTyCode :
    isDependentBinaryFormer .gen_sigmaTyCode = true := rfl

mutual

/-- The cascade-free typing judgment.  Core arms `var` + `conv`, the
nullary `universeFormation` shape-arm (`Type@(e, flag) : Type@(lsucc e,
flag)` — stated directly via the `universeCodeCell` smart ctor, since the
universe shape has exactly the one generator `gen_universeCode` so the
smart ctor IS the shape membership — no whitelist predicate needed), plus
ONE per-shape `dependentBinaryFormation` arm — the dependent-binary
type-formation shape — that consumes the `Generator` metadata predicate
`isDependentBinaryFormer` (the whitelist hypothesis `isBinaryFormer`).
The subject is `.mkGen generator payload children` over a `generator`
GENERIC within the shape (admitted by the whitelist); the output
universe level is the explicit INDEX `LevelExpr.lmax domainLevel
codomainLevel`.  The `[0, 1]` shape constraint is forced not by an
equality hypothesis but by the `childrenTyped` spine, whose conclusion
fixes the children to `binderShape …` (index definitionally `[0, 1]`). -/
inductive HasTypeGen (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | var {scope : Nat} (context : TypingContext profile scope)
      (index : Fin scope) :
      HasTypeGen profile context (variableCell index) (context.lookup index)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeGen profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeGen profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeGen profile context subject reclassifier
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag) :
      HasTypeGen profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)
  | dependentBinaryFormation {scope : Nat}
      (context : TypingContext profile scope)
      (generator : Generator)
      (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (isBinaryFormer : isDependentBinaryFormer generator = true)
      (childrenTyped :
        DependentBinaryFormationChildren profile context
          domainLevel codomainLevel flag children) :
      HasTypeGen profile context (.mkGen generator payload children)
        (universeCodeCell
          (LevelExpr.lmax domainLevel codomainLevel) flag)

/-- The typed-children SPINE for the `[0, 1]` dependent-binary shape.
Its INDEX SIGNATURE references ONLY `PolyProfile`, `Nat`, `LevelExpr`,
`UniverseFlag`, `List Nat`, `TypingContext`, `RawTerm`, and
`RawTermChildren` — NEVER `HasTypeGen` (the mutual-index rule).  It
references `HasTypeGen` only POSITIVELY in constructor premises.

The single constructor `dependentBinary` takes both children's typing
premises at once (the `[0, 1]` shape is a fixed two-element list, so no
head-first list peeling is needed), and threads the dependent-binder
context extension: `codomainTyped` types the codomain child in the
context EXTENDED by the domain child, at scope `parentScope + 1`.  Its
conclusion fixes the children to `RawTermChildren.binderShape …` (index
definitionally `[0, 1]`). -/
inductive DependentBinaryFormationChildren (profile : PolyProfile) :
    {parentScope : Nat} → {binderShifts : List Nat} →
      TypingContext profile parentScope →
      LevelExpr → LevelExpr → UniverseFlag →
      RawTermChildren binderShifts parentScope → Prop where
  | dependentBinary {parentScope : Nat}
      (context : TypingContext profile parentScope)
      (domainCode : RawTerm parentScope)
      (codomainCode : RawTerm (parentScope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (domainTyped :
        HasTypeGen profile context domainCode
          (universeCodeCell domainLevel flag))
      (codomainTyped :
        HasTypeGen profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag)) :
      DependentBinaryFormationChildren profile context
        domainLevel codomainLevel flag
        (RawTermChildren.binderShape domainCode codomainCode)

end

/-- Smoke lemma: the `dependentBinaryFormation` arm reconstructs
Pi-formation.  Given the domain code typed at `Type@(domainLevel, flag)`
and the codomain code typed at `Type@(codomainLevel, flag)` UNDER THE
DOMAIN BINDER, the `piTyCodeCell` is classified by `Type@(lmax
domainLevel codomainLevel, flag)` — the same conclusion as
`HasType.piFormation`, derived through the per-shape Generator-metadata
arm.  Demonstrates the shape-arm covers `gen_piTyCode` with no
per-generator code. -/
theorem hasTypeGen_piFormation_viaShapeArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeGen profile context domainCode
        (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeGen profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    HasTypeGen profile context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell
        (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasTypeGen.dependentBinaryFormation context .gen_piTyCode ()
    (RawTermChildren.binderShape domainCode codomainCode)
    domainLevel codomainLevel flag
    isDependentBinaryFormer_piTyCode
    (DependentBinaryFormationChildren.dependentBinary
      context domainCode codomainCode
      domainLevel codomainLevel flag domainTyped codomainTyped)

/-- Smoke lemma: the SAME `dependentBinaryFormation` arm reconstructs
Sigma-formation (`gen_sigmaTyCode`), with ZERO new code — one metadata
row (`isDependentBinaryFormer_sigmaTyCode`) suffices.  This is the P13
cascade-freedom witness: a second `[0, 1]` former reuses the one arm. -/
theorem hasTypeGen_sigmaFormation_viaShapeArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeGen profile context domainCode
        (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeGen profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    HasTypeGen profile context (sigmaTyCodeCell domainCode codomainCode)
      (universeCodeCell
        (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasTypeGen.dependentBinaryFormation context .gen_sigmaTyCode ()
    (RawTermChildren.binderShape domainCode codomainCode)
    domainLevel codomainLevel flag
    isDependentBinaryFormer_sigmaTyCode
    (DependentBinaryFormationChildren.dependentBinary
      context domainCode codomainCode
      domainLevel codomainLevel flag domainTyped codomainTyped)

end FX1Poly.Typed

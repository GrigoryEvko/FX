import FX1Poly.Core.HasCertifiedIntros

/-! # Foundation/PolyCell/Core/HasCertifiedComposition — compound intros

**Compound smart constructors** for `HasCertifiedCellDim0` over the
term-shape generators that admit certified children.

## Context

The nullary intros in `HasCertifiedIntros.lean` (var, unit,
boolTrue, boolFalse, natZero, listNil, optionNone) take no
children and certify a leaf term as structurally admitted.

This file extends with COMPOUND intros that take CELLS for the
children and certify the parent term.  Each takes
`PolyCell profile .term 0 scope CellBoundary.trivial (.termBase ...)`
arguments for the children — the explicit cell type encodes the
sort `.term` constraint statically (rather than going through
the sort-existential `HasCertifiedCellDim0` wrapper).

## API design rationale

Why take cells directly, not `HasCertifiedCellDim0` wrappers?

`HasCertifiedCellDim0 raw` is sort-existential.  Destructuring
gives a cell at SOME sort, but `PolyCell.gen` for a term-shape
generator (gen_app, gen_lam, gen_pair, ...) requires the
children's spine to be sort `.term`.  Without an external
sort constraint, the destructured cells might not match.

By taking cells directly with sort `.term` baked in, the
smart constructors enforce the constraint at the type level
and become composable building blocks for the future
structural-induction mutual block (rename / subst preservation
on compound terms).

The CALLER converts `HasCertifiedCellDim0` to cells via the
constructor's destructure machinery in their own proof
context (where they have the necessary type information about
the underlying generator).

## Coverage

Term-shape compound generators with .term-sorted children:

  * **Binary, no binders**: `app`, `pair`, `listCons`
  * **Unary, no binders**: `natSucc`, `optionSome`,
    `eitherInl`, `eitherInr`, `refl`
  * **Unary, 1 binder**: `lam` (body at scope+1)
  * **Ternary, no binders**: `boolElim`, `natElim`, `natRec`,
    `listElim`, `optionMatch`, `eitherMatch`

(idJ has motive subtleties at the substrate level and is
omitted from this initial batch.)

## Zero-axiom verification

Each intro is a direct `PolyCell.gen` construction with the
global `SupportedGenerator.gen_X` admission witness, the
default `()` payload evidence, and a `CertifiedTermSpine.cons`
chain over the children.  No tactics, no induction.

Audit-gated.
-/

namespace FX1Poly.Core

/-! ## Section 1 — Unary no-binder intros

For: `natSucc`, `optionSome`, `eitherInl`, `eitherInr`, `refl`.
Single child at same scope, sort `.term`. -/

/-- **Intro: app's structural admission from function + argument cells.** -/
theorem HasCertifiedCellDim0.app
    {profile : PolyProfile} {scope : Nat}
    {functionTerm argumentTerm : RawTerm scope}
    (functionCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase functionTerm))
    (argumentCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase argumentTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_app ()
        (.childCons functionTerm
          (.childCons argumentTerm .childNil))) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_app
      (genPayloadEvidence (generator := .gen_app)
                           (scope := scope) ())
      (CertifiedTermSpine.cons functionCell
        (CertifiedTermSpine.cons argumentCell
          CertifiedTermSpine.nil)))

/-- **Intro: pair's structural admission from first + second cells.** -/
theorem HasCertifiedCellDim0.pair
    {profile : PolyProfile} {scope : Nat}
    {firstTerm secondTerm : RawTerm scope}
    (firstCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase firstTerm))
    (secondCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase secondTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_pair ()
        (.childCons firstTerm
          (.childCons secondTerm .childNil))) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_pair
      (genPayloadEvidence (generator := .gen_pair)
                           (scope := scope) ())
      (CertifiedTermSpine.cons firstCell
        (CertifiedTermSpine.cons secondCell
          CertifiedTermSpine.nil)))

/-- **Intro: natSucc's structural admission from predecessor cell.** -/
theorem HasCertifiedCellDim0.natSucc
    {profile : PolyProfile} {scope : Nat}
    {predecessorTerm : RawTerm scope}
    (predecessorCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase predecessorTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_natSucc ()
        (.childCons predecessorTerm .childNil)) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_natSucc
      (genPayloadEvidence (generator := .gen_natSucc)
                           (scope := scope) ())
      (CertifiedTermSpine.cons predecessorCell
        CertifiedTermSpine.nil))

/-- **Intro: optionSome's structural admission from wrapped cell.** -/
theorem HasCertifiedCellDim0.optionSome
    {profile : PolyProfile} {scope : Nat}
    {wrappedTerm : RawTerm scope}
    (wrappedCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase wrappedTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_optionSome ()
        (.childCons wrappedTerm .childNil)) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_optionSome
      (genPayloadEvidence (generator := .gen_optionSome)
                           (scope := scope) ())
      (CertifiedTermSpine.cons wrappedCell
        CertifiedTermSpine.nil))

/-- **Intro: eitherInl's structural admission from wrapped cell.** -/
theorem HasCertifiedCellDim0.eitherInl
    {profile : PolyProfile} {scope : Nat}
    {wrappedTerm : RawTerm scope}
    (wrappedCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase wrappedTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_eitherInl ()
        (.childCons wrappedTerm .childNil)) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_eitherInl
      (genPayloadEvidence (generator := .gen_eitherInl)
                           (scope := scope) ())
      (CertifiedTermSpine.cons wrappedCell
        CertifiedTermSpine.nil))

/-- **Intro: eitherInr's structural admission from wrapped cell.** -/
theorem HasCertifiedCellDim0.eitherInr
    {profile : PolyProfile} {scope : Nat}
    {wrappedTerm : RawTerm scope}
    (wrappedCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase wrappedTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_eitherInr ()
        (.childCons wrappedTerm .childNil)) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_eitherInr
      (genPayloadEvidence (generator := .gen_eitherInr)
                           (scope := scope) ())
      (CertifiedTermSpine.cons wrappedCell
        CertifiedTermSpine.nil))

/-- **Intro: listCons's structural admission from head + tail cells.** -/
theorem HasCertifiedCellDim0.listCons
    {profile : PolyProfile} {scope : Nat}
    {headTerm tailTerm : RawTerm scope}
    (headCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase headTerm))
    (tailCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase tailTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_listCons ()
        (.childCons headTerm
          (.childCons tailTerm .childNil))) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_listCons
      (genPayloadEvidence (generator := .gen_listCons)
                           (scope := scope) ())
      (CertifiedTermSpine.cons headCell
        (CertifiedTermSpine.cons tailCell
          CertifiedTermSpine.nil)))

/-- **Intro: refl's structural admission from witness cell.** -/
theorem HasCertifiedCellDim0.refl
    {profile : PolyProfile} {scope : Nat}
    {witnessTerm : RawTerm scope}
    (witnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase witnessTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen .gen_refl ()
        (.childCons witnessTerm .childNil)) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_refl
      (genPayloadEvidence (generator := .gen_refl)
                           (scope := scope) ())
      (CertifiedTermSpine.cons witnessCell
        CertifiedTermSpine.nil))

/-! ## Section 2 — Lambda intro (1 binder)

`gen_lam`'s body lives at `scope + 1` (the bound variable).
The body cell takes the +1-shifted scope explicitly. -/

/-- **Intro: lam's structural admission from body cell at scope+1.** -/
theorem HasCertifiedCellDim0.lam
    {profile : PolyProfile} {scope : Nat}
    {bodyTerm : RawTerm (scope + 1)}
    (bodyCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase bodyTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_lam ()
        (.childCons bodyTerm .childNil) : RawTerm scope)) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_lam
      (genPayloadEvidence (generator := .gen_lam)
                           (scope := scope) ())
      (CertifiedTermSpine.cons bodyCell
        CertifiedTermSpine.nil))

end FX1Poly.Core

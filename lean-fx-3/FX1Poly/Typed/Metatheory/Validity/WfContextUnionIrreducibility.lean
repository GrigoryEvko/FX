import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Metatheory.Canonicity.Core.ClosedNatCanonicity

/-! # FX1Poly/Typed/Metatheory/Validity/WfContextUnionIrreducibility — TYTAB-2 WFCTX

**Verdict: `WfContextUnion` is an IRREDUCIBLE presupposition, not a derivable theorem.**

The no-compromise target for TYTAB-2-WFCTX was *regularity* — deriving the context
well-formedness `WfContextUnion context` from a typing `HasTypeUnion profile context subject
classifier`, the way a fully-presupposition-free presentation would.  This file proves, zero-axiom,
that regularity is **FALSE** for the native union judgment, so `WfContextUnion` must stay a
threaded hypothesis (as it already is, in validity `§classifierIsType` and the SR closers).

## Why regularity fails — the minimal irreducible core

The union judgment `HasTypeUnionOver` has two structural LEAF arms that carry **no**
well-formedness premise on the context:

  * `var`     — `HasTypeUnionOver bundle profile context (variableCell index) (context.lookup index)`
  * `universeFormation` —
      `HasTypeUnionOver bundle profile context (universeCodeCell L f) (universeCodeCell L.lsucc f)`

Both fire in an ARBITRARY context, including an ill-formed one.  This is the deliberate
well-scoped-but-not-well-formed discipline (a context is a length-indexed list of *raw* binders;
nothing forces each binder to be a type).  `universeFormation` is the sharper witness: it needs
nothing whatsoever about the context, so a single derivation lives in `(.empty.cons badBinding)`
for *any* `badBinding`, well-typed or not.

The reductio:

  1. `regularity` applied to a `universeFormation` derivation in `(.empty.cons badBinding)` would
     yield `WfContextUnion (.empty.cons badBinding)`, hence (`headIsType`)
     `UnionClassifierIsType .empty badBinding` — i.e. EVERY closed raw term would be a type
     (`regularityImpliesEveryClosedTermIsType`).
  2. That is absurd: `natSuccCell child` is a VALUE.  Any union typing of it has classifier
     `Conv natTypeCell _` (`invertAtNatSuccHead`), and `natTypeCell` is never `Conv` a universe
     code (`Conv.natTypeCell_not_universeCode`) — so it is provably not a type
     (`natSuccCellNotUnionType`).
  3. Therefore `¬ regularity` (`regularityRefuted`).

## What IS recoverable (the honest positive, shipped in `HasTypeUnionValidity`)

`WfContextUnion` is not derivable, but it IS the right presupposition: it is preserved going under
every binder (`WfContextUnion.cons` + `WfContextUnion.weakenUnderBinding`) and it discharges
per-variable validity on demand (`WfContextUnion.lookupIsType`).  So the cost of irreducibility is
exactly one threaded hypothesis, and nothing more — the binder arms never need a side condition
beyond their own formation premises plus the inherited `WfContextUnion`.

Every declaration below is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` (audited in `FX1PolyAudit/AuditWfContextUnionIrreducibility`). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The shape of the **regularity** claim that TYTAB-2-WFCTX set out to derive: every typing
presupposes a union-well-formed context.  Refuted below (`regularityRefuted`). -/
abbrev UnionRegularityClaim (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeUnion profile context subject classifier → WfContextUnion context

/-- **A successor value is not a type.**  `natSuccCell child` introduces a `nat`, so every union
typing of it lands at a classifier `Conv natTypeCell _` (`invertAtNatSuccHead`), and `natTypeCell`
is rigidly distinct from every universe code (`Conv.natTypeCell_not_universeCode`).  This is the
concrete non-type that breaks regularity. -/
theorem natSuccCellNotUnionType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (child : RawTerm scope) :
    ¬ UnionClassifierIsType profile context (natSuccCell child) := by
  rintro ⟨_levelExpr, _flag, typed⟩
  exact Conv.natTypeCell_not_universeCode
    (HasTypeUnion.invertAtNatSuccHead typed rfl).1

/-- **Regularity would collapse the type/term distinction.**  The premise-free `universeFormation`
leaf types `Type@0 : Type@1` in the context `(.empty.cons badBinding)` regardless of `badBinding`;
regularity then forces `badBinding` itself to be a type.  Stated for an arbitrary closed raw term,
this says regularity makes EVERY closed term a union type — the heart of the reductio. -/
theorem regularityImpliesEveryClosedTermIsType {profile : PolyProfile}
    (regularity : UnionRegularityClaim profile) (badBinding : RawTerm 0) :
    UnionClassifierIsType profile TypingContext.empty badBinding := by
  have derivation :
      HasTypeUnion profile (TypingContext.empty.cons badBinding)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    HasTypeUnion.universeFormation (TypingContext.empty.cons badBinding)
      LevelExpr.lzero UniverseFlag.standard
  exact WfContextUnion.headIsType (regularity derivation)

/-- **★ Regularity is FALSE — `WfContextUnion` is irreducible.**  Combining the collapse with the
concrete non-type `natSuccCell natZeroCell`: regularity would make that successor value a type,
contradicting `natSuccCellNotUnionType`.  Hence `WfContextUnion` cannot be recovered from a typing
derivation and must remain a threaded presupposition. -/
theorem regularityRefuted {profile : PolyProfile} :
    ¬ UnionRegularityClaim profile := by
  intro regularity
  exact natSuccCellNotUnionType natZeroCell
    (regularityImpliesEveryClosedTermIsType regularity (natSuccCell natZeroCell))

end FX1Poly.Typed

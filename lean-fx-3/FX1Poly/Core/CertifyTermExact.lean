import FX1Poly.Core.CertifyTermSpine

/-! # Foundation/PolyCell/Core/CertifyTermExact — generator dispatch

This file ships `certifyTermExact?`: the generator-dispatch function
that, given a `Generator + payload + children`, certifies the term
form by:

1. Looking up the generator's admission via `supportedGenerator?`
2. Looking up the payload's evidence via `genPayloadEvidence?`
3. Recursively certifying the children spine via
   `certifyTermSpine?`
4. Packaging the result via `packageGen`

This is the dispatcher used by the recursive certifier (#162) when
it pattern-matches on a raw `.termBase (.mkGen generator payload
children)` shape.

## The coherence-as-data bridge

The structural challenge: `certifyTermSpine?` accepts a spine at
ANY `binderShifts : List Nat` with a coherence proof
`binderShifts = childSpecs.map (·.scopeShift)`.  `certifyTermExact?`
passes:

* `binderShifts := generator.binderShifts` (inferred from children's
  type)
* `coherence := (Generator.childSpecs_scopeShifts_eq_binderShifts
  generator).symm`

The coherence lemma is provable by `cases g <;> rfl` (propext-free)
and ships axiom-clean.  Inside `certifyTermSpine?`, the tactic-mode
`subst coherence` normalizes the spine type — so the output is at
`generator.binderShifts`, matching what `PolyCell.gen` expects
exactly.  No `▸` chains here.

This is the "thread the equation as data" pattern: pass the proof
as an argument, let the callee absorb it via `subst`.

## Per-profile dispatch

Under fxProfile, both `supportedGenerator? generator` and
`genPayloadEvidence? payload` always return `.some` — the
`.none` rejection paths are dead code.  Future restricted
profiles will exercise these paths.

The function ships the rejection paths defensively so that
restricted-profile variants don't need ANY changes to
`certifyTermExact?` — they just refine the lookups.

## Zero-axiom verification

Pattern matching on `Option` and `Except` (closed inductives, full
enumeration).  Coherence proof comes from the axiom-clean
`Generator.childSpecs_scopeShifts_eq_binderShifts` lemma.  Calls to
`certifyTermSpine?` and `packageGen` inherit their
axiom-cleanliness.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Generator dispatch: certify a raw term-former by:
admission + payload evidence + recursive spine certification +
packaging.

Used by the recursive certifier (#162) when it encounters a raw
`.termBase (.mkGen ...)`.  The `recursiveCertifier` is the
forward-declared callback that #162 ties to itself.

Implementation: three-step dispatch.  No `▸` transports — the
coherence equation is passed as data to `certifyTermSpine?`
which absorbs it via internal `subst`. -/
def certifyTermExact? {profile : PolyProfile} {scope : Nat}
    (recursiveCertifier :
      (scope : Nat) → (raw : RawCell scope) →
      Except CellCheckRejection (CertifiedCell profile scope))
    (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    Except CellCheckRejection (CertifiedCell profile scope) :=
  -- Step 1: Generator admission lookup
  match supportedGenerator? generator with
  | none => .error .unknownGenerator
  | some admission =>
    -- Step 2: Payload evidence lookup
    match genPayloadEvidence? payload with
    | none => .error .badPayload
    | some payloadEvidence =>
      -- Step 3: Certify the children spine at generator.binderShifts
      -- Coherence: binderShifts = childSpecs.map ·.scopeShift, via .symm
      -- of the standard coherence lemma
      let coherence :=
        (Generator.childSpecs_scopeShifts_eq_binderShifts
          generator).symm
      match certifyTermSpine? recursiveCertifier
              generator.childSpecs coherence children with
      | .ok spine =>
        -- Step 4: Package the gen cell via packageGen
        .ok (packageGen admission payloadEvidence spine)
      | .error rejection => .error rejection

end FX1Poly.Core

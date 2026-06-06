import FX1Poly.Typed.IsTypeDescDecidableGeneric
import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.WfContextDescStronglyNormalizing
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/HasTypeDescNativeDecidable
    — native `Decidable (HasTypeDesc Γ t T)` for the formation engine (HT-A4 bricks B2 + B3, off old `HasType`)

The full formation typing judgment `HasTypeDesc Γ t T` is DECIDABLE, built ENTIRELY from `HasTypeDesc` pieces
over `WfContextDesc` — NO `HasType.toHasType` oracle.  The shipped `HasTypeDesc.decidableOfWellFormed`
(`HasTypeDescDecidable.lean`) still routes through the bespoke `HasType.decidableOfWellFormed`; this file
supplies the native replacement `HasTypeDesc.decidableOfWellFormedNative`.

## The two bricks (now CASCADE-FREE)

* **`HasTypeDesc.inferWithWitness` (B2)** — principal-type synthesis: a subject either has a principal type
  (a `Σ'`-packaged `HasTypeDesc` derivation) or has NO type at any classifier (a `∀ T, HasTypeDesc Γ t T →
  False` refutation).  NON-recursive: `var` synthesises its lookup, `gen_universeCode` its successor universe,
  and EVERY OTHER head delegates to the cascade-free `IsTypeDesc.decideTypeGeneric` — a former's principal
  type IS the universe code that `decideTypeGeneric` returns, and a non-typeable head is refuted by mapping any
  putative typing back through `subjectRootGeneratorGeneric` + `inversionFormerWithConvGeneric` + the generic
  `genFormation` to an `IsTypeDesc` witness that contradicts the `.inr`.  Names NO formation generator — a new
  formation row (`listCode`/…) is absorbed zero-touch (the FRAME-2 property), with no Π/Σ enumeration and no
  `typingRuleDescOf_isPiOrSigma` else-branch.

* **`HasTypeDesc.decidableOfWellFormedNative` (B3)** — the decision.  Synthesise the subject's principal type
  `T0` (`inferWithWitness`); then `HasTypeDesc Γ t T ⟺ Conv T0 T` (forward: uniqueness of the principal type;
  backward: the `conv` rule).  The `Conv` is decided by `Conv.decidableOfStronglyNormalizing` — `T0` is SN by
  native validity (`classifierStronglyNormalizingNative`), and `T` is SN once gated through the cascade-free
  `IsTypeDesc.decidableOfWellFormedGeneric` (B1d): if `T` is NOT a type then `HasTypeDesc Γ t T` is impossible
  (`classifierIsTypeDescNative`), and if it IS a type it is SN (`IsTypeDesc.isStronglyNormalizing`).  The
  `isFalse` of a genuine `Conv` mismatch refutes via `uniquenessNative`.

## Zero-axiom verification

`inferWithWitness` is a head `match` (no recursion) whose `inl` witnesses are the formation constructors /
`decideTypeGeneric`'s universe witness and whose `inr` refutations compose `subjectRootGeneratorGeneric` +
`inversionFormerWithConvGeneric` + the generic `genFormation`; the decision composes it with
`IsTypeDesc.decidableOfWellFormedGeneric` + `Conv.decidableOfStronglyNormalizing` + the shipped native validity
/ SN bridges.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Principal-type synthesis for the formation engine** (HT-A4 B2, cascade-free).  Either the subject has a
principal type (a `HasTypeDesc` derivation) or it inhabits no type at any classifier.  NON-recursive: `var` →
its context lookup; `gen_universeCode` → the successor universe code; ANY OTHER head delegates to
`IsTypeDesc.decideTypeGeneric` — its `.inl` universe witness IS the head's principal type; its `.inr` (the head
is not a type-code) refutes any putative typing by reconstructing the `IsTypeDesc` witness it denies (a
formation-typed non-var non-universe subject inverts generically to a telescope, whence the generic
`genFormation` re-derives the universe code).  Names NO formation generator. -/
def HasTypeDesc.inferWithWitness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (subject : RawTerm scope) :
    PSum
      (Σ' (principalType : RawTerm scope), HasTypeDesc profile context subject principalType)
      (∀ (anyType : RawTerm scope), HasTypeDesc profile context subject anyType → False) :=
  match subject with
  | .mkGen generator payload children =>
      if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have cellIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children) = variableCell payload := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact .inl ⟨context.lookup payload, by
          rw [cellIsVariable]; exact HasTypeDesc.var context payload⟩
      else if hUniverse : generator = Generator.gen_universeCode then by
        subst hUniverse
        have cellIsUniverseCode :
            (RawTerm.mkGen Generator.gen_universeCode payload children)
              = universeCodeCell payload.1 payload.2 := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact .inl ⟨universeCodeCell payload.1.lsucc payload.2, by
          rw [cellIsUniverseCode]; exact HasTypeDesc.universeFormation context payload.1 payload.2⟩
      else by
        exact (match IsTypeDesc.decideTypeGeneric wellFormed (.mkGen generator payload children) with
          | .inl ⟨levelExpr, flag, typed⟩ =>
              .inl ⟨universeCodeCell levelExpr flag, typed⟩
          | .inr notType =>
              .inr (fun _anyType typed => by
                apply notType
                rcases typed.subjectRootGeneratorGeneric with
                  isVariable | isUniverseCode | ⟨rule, isFormer⟩
                · exact absurd isVariable hVariable
                · exact absurd isUniverseCode hUniverse
                · obtain ⟨levels, telFlag, telescope, _convToCode⟩ :=
                    HasTypeDesc.inversionFormerWithConvGeneric typed isFormer rfl
                  refine ⟨lmaxAll levels, telFlag, ?_⟩
                  have formerTyped :=
                    HasTypeDesc.genFormation context generator payload children levels telFlag rule
                      isFormer telescope
                  rw [typingRuleDescOf_outputIsUniverseFormer isFormer] at formerTyped
                  exact formerTyped))

/-- **Native `Decidable (HasTypeDesc Γ t T)`** (HT-A4 B3) — decide the full formation typing judgment, off the
old `HasType` engine.  Synthesise the subject's principal type `T0` (`inferWithWitness`); the typing holds iff
`Conv T0 classifier`.  The `Conv` is decided by `Conv.decidableOfStronglyNormalizing` (`T0` SN by
`classifierStronglyNormalizingNative`; `classifier` SN once gated through the cascade-free
`IsTypeDesc.decidableOfWellFormedGeneric` — a non-type classifier makes the typing impossible via
`classifierIsTypeDescNative`).  Forward through the `conv` rule (reclassifying `T0` to the universe-code-typed
`classifier`); `isFalse` refutes via `uniquenessNative`.  The native twin of the shipped
`HasTypeDesc.decidableOfWellFormed`. -/
def HasTypeDesc.decidableOfWellFormedNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (subject classifier : RawTerm scope) :
    Decidable (HasTypeDesc profile context subject classifier) :=
  match HasTypeDesc.inferWithWitness wellFormed subject with
  | .inr subjectHasNoType => isFalse (subjectHasNoType classifier)
  | .inl ⟨principalType, principalTyped⟩ =>
      match IsTypeDesc.decidableOfWellFormedGeneric wellFormed classifier with
      | isFalse classifierNotType =>
          isFalse fun typed =>
            classifierNotType (HasTypeDesc.classifierIsTypeDescNative wellFormed typed)
      | isTrue classifierIsType =>
          match Conv.decidableOfStronglyNormalizing
              (HasTypeDesc.classifierStronglyNormalizingNative wellFormed principalTyped)
              (IsTypeDesc.isStronglyNormalizing classifierIsType) with
          | isTrue convertsToClassifier =>
              isTrue (by
                obtain ⟨levelExpr, flag, classifierTypedAtUniverse⟩ := classifierIsType
                exact HasTypeDesc.conv levelExpr flag principalTyped convertsToClassifier
                  classifierTypedAtUniverse)
          | isFalse doesNotConvert =>
              isFalse fun typed =>
                doesNotConvert (HasTypeDesc.uniquenessNative principalTyped wellFormed typed)

end FX1Poly.Typed

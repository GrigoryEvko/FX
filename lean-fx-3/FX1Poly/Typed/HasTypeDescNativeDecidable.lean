import FX1Poly.Typed.IsTypeDescDecidable
import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.WfContextDescStronglyNormalizing
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/HasTypeDescNativeDecidable
    — native `Decidable (HasTypeDesc Γ t T)` for the formation engine (HT-A4 bricks B2 + B3, off old `HasType`)

The full formation typing judgment `HasTypeDesc Γ t T` is DECIDABLE, built ENTIRELY from `HasTypeDesc` pieces
over `WfContextDesc` — NO `HasType.toHasType` oracle.  The shipped `HasTypeDesc.decidableOfWellFormed`
(`HasTypeDescDecidable.lean`) still routes through the bespoke `HasType.decidableOfWellFormed`; this file
supplies the native replacement `HasTypeDesc.decidableOfWellFormedNative` (the consumer-site migration to it,
then deletion of the old engine, is HT-B / HT-C).

## The two bricks

* **`HasTypeDesc.inferWithWitness` (B2)** — principal-type synthesis: a subject either has a principal type
  (a `Σ'`-packaged `HasTypeDesc` derivation) or has NO type at any classifier (a `∀ T, HasTypeDesc Γ t T →
  False` refutation).  NON-recursive: `var` synthesises its lookup, `gen_universeCode` its successor universe,
  Π/Σ-formers reuse the shipped `IsTypeDesc.decideWithWitness` (B1) on their children, and every other head is
  refuted by `subjectRootGeneratorGeneric` (a formation-typed subject is rooted at var / universe / a formation
  former).  The `HasTypeDesc` analogue of the bespoke principal-type inference, off the old engine.

* **`HasTypeDesc.decidableOfWellFormedNative` (B3)** — the decision.  Synthesise the subject's principal type
  `T0` (`inferWithWitness`); then `HasTypeDesc Γ t T ⟺ Conv T0 T` (forward: uniqueness of the principal type;
  backward: the `conv` rule).  The `Conv` is decided by `Conv.decidableOfStronglyNormalizing` — `T0` is SN by
  native validity (`classifierStronglyNormalizingNative`), and `T` is SN once gated through the now-decidable
  `IsTypeDesc Γ T` (B1d): if `T` is NOT a type then `HasTypeDesc Γ t T` is impossible (`classifierIsTypeDescNative`),
  and if it IS a type it is SN (`IsTypeDesc.isStronglyNormalizing`).  The `isFalse` of a genuine `Conv` mismatch
  refutes via `uniquenessNative`.

## Zero-axiom verification

`inferWithWitness` is a head `match` (no recursion) whose `inl` witnesses are the formation constructors /
`hasTypeDesc_{pi,sigma}Formation_viaGenArm` and whose `inr` refutations compose the shipped native inversions +
`uniquenessNative` + `subjectRootGeneratorGeneric`; the decision composes it with `IsTypeDesc.decidableOfWellFormed`
+ `Conv.decidableOfStronglyNormalizing` + the shipped native validity / SN bridges.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Principal-type synthesis for the formation engine** (HT-A4 B2).  Either the subject has a principal
type (a `HasTypeDesc` derivation) or it inhabits no type at any classifier.  NON-recursive: `var` →
its context lookup; `gen_universeCode` → the successor universe code; Π/Σ-former → reuse
`IsTypeDesc.decideWithWitness` on the two children (typeable iff both are types at a shared flag, built via
`hasTypeDesc_{pi,sigma}Formation_viaGenArm`); any other head → refuted by `subjectRootGeneratorGeneric`.

The `inr` refutations: a child that is not a type contradicts the children-extraction
`inversionPiCodeChildren` / `inversionSigmaCodeChildren`; a flag mismatch contradicts
`HasTypeDesc.uniquenessNative` (each child's universe flag is derivation-unique, and the former forces them
shared); a non-former head contradicts `subjectRootGeneratorGeneric`. -/
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
      else if hPi : generator = Generator.gen_piTyCode then
        match generator, children, hPi with
        | .gen_piTyCode, .childCons domainCode (.childCons codomainCode .childNil), rfl =>
              match IsTypeDesc.decideWithWitness wellFormed domainCode with
              | .inr domainNotType =>
                  .inr fun _anyType typed => by
                    obtain ⟨domainLevel, _codomainLevel, sharedFlag, domainTyped, _⟩ :=
                      HasTypeDesc.inversionPiCodeChildren typed
                    exact domainNotType ⟨domainLevel, sharedFlag, domainTyped⟩
              | .inl ⟨domainLevel, domainFlag, domainTyped⟩ =>
                  match IsTypeDesc.decideWithWitness
                      (WfContextDesc.cons wellFormed ⟨domainLevel, domainFlag, domainTyped⟩)
                      codomainCode with
                  | .inr codomainNotType =>
                      .inr fun _anyType typed => by
                        obtain ⟨_domainLevel, codomainLevel, sharedFlag, _, codomainTyped⟩ :=
                          HasTypeDesc.inversionPiCodeChildren typed
                        exact codomainNotType ⟨codomainLevel, sharedFlag, codomainTyped⟩
                  | .inl ⟨codomainLevel, codomainFlag, codomainTyped⟩ =>
                      if hFlag : domainFlag = codomainFlag then by
                        subst hFlag
                        exact .inl
                          ⟨universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) domainFlag,
                            hasTypeDesc_piFormation_viaGenArm context domainCode codomainCode
                              domainLevel codomainLevel domainFlag domainTyped codomainTyped⟩
                      else
                        .inr fun _anyType typed => by
                          obtain ⟨_invDomainLevel, _invCodomainLevel, _invFlag,
                            invDomainTyped, invCodomainTyped⟩ :=
                            HasTypeDesc.inversionPiCodeChildren typed
                          obtain ⟨_, domainFlagAgree⟩ :=
                            universeCodeCell_inj_of_conv
                              (HasTypeDesc.uniquenessNative domainTyped wellFormed invDomainTyped)
                          obtain ⟨_, codomainFlagAgree⟩ :=
                            universeCodeCell_inj_of_conv
                              (HasTypeDesc.uniquenessNative codomainTyped
                                (WfContextDesc.cons wellFormed
                                  ⟨domainLevel, domainFlag, domainTyped⟩)
                                invCodomainTyped)
                          exact hFlag (domainFlagAgree.trans codomainFlagAgree.symm)
      else if hSigma : generator = Generator.gen_sigmaTyCode then
        match generator, children, hSigma with
        | .gen_sigmaTyCode, .childCons domainCode (.childCons codomainCode .childNil), rfl =>
              match IsTypeDesc.decideWithWitness wellFormed domainCode with
              | .inr domainNotType =>
                  .inr fun _anyType typed => by
                    obtain ⟨domainLevel, _codomainLevel, sharedFlag, domainTyped, _⟩ :=
                      HasTypeDesc.inversionSigmaCodeChildren typed
                    exact domainNotType ⟨domainLevel, sharedFlag, domainTyped⟩
              | .inl ⟨domainLevel, domainFlag, domainTyped⟩ =>
                  match IsTypeDesc.decideWithWitness
                      (WfContextDesc.cons wellFormed ⟨domainLevel, domainFlag, domainTyped⟩)
                      codomainCode with
                  | .inr codomainNotType =>
                      .inr fun _anyType typed => by
                        obtain ⟨_domainLevel, codomainLevel, sharedFlag, _, codomainTyped⟩ :=
                          HasTypeDesc.inversionSigmaCodeChildren typed
                        exact codomainNotType ⟨codomainLevel, sharedFlag, codomainTyped⟩
                  | .inl ⟨codomainLevel, codomainFlag, codomainTyped⟩ =>
                      if hFlag : domainFlag = codomainFlag then by
                        subst hFlag
                        exact .inl
                          ⟨universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) domainFlag,
                            hasTypeDesc_sigmaFormation_viaGenArm context domainCode codomainCode
                              domainLevel codomainLevel domainFlag domainTyped codomainTyped⟩
                      else
                        .inr fun _anyType typed => by
                          obtain ⟨_invDomainLevel, _invCodomainLevel, _invFlag,
                            invDomainTyped, invCodomainTyped⟩ :=
                            HasTypeDesc.inversionSigmaCodeChildren typed
                          obtain ⟨_, domainFlagAgree⟩ :=
                            universeCodeCell_inj_of_conv
                              (HasTypeDesc.uniquenessNative domainTyped wellFormed invDomainTyped)
                          obtain ⟨_, codomainFlagAgree⟩ :=
                            universeCodeCell_inj_of_conv
                              (HasTypeDesc.uniquenessNative codomainTyped
                                (WfContextDesc.cons wellFormed
                                  ⟨domainLevel, domainFlag, domainTyped⟩)
                                invCodomainTyped)
                          exact hFlag (domainFlagAgree.trans codomainFlagAgree.symm)
      else
        .inr fun _anyType typed => by
          rcases typed.subjectRootGeneratorGeneric with
            isVariable | isUniverseCode | ⟨rule, isFormer⟩
          · exact hVariable isVariable
          · exact hUniverse isUniverseCode
          · rcases typingRuleDescOf_isPiOrSigma isFormer with hIsPi | hIsSigma
            · exact hPi hIsPi
            · exact hSigma hIsSigma

/-- **Native `Decidable (HasTypeDesc Γ t T)`** (HT-A4 B3) — decide the full formation typing judgment, off
the old `HasType` engine.  Synthesise the subject's principal type `T0` (`inferWithWitness`); the typing holds
iff `Conv T0 classifier`.  The `Conv` is decided by `Conv.decidableOfStronglyNormalizing` (`T0` SN by
`classifierStronglyNormalizingNative`; `classifier` SN once gated through `IsTypeDesc.decidableOfWellFormed` —
a non-type classifier makes the typing impossible via `classifierIsTypeDescNative`).  Forward through the
`conv` rule (reclassifying `T0` to the universe-code-typed `classifier`); `isFalse` refutes via
`uniquenessNative`.  The native twin of the shipped `HasTypeDesc.decidableOfWellFormed`. -/
def HasTypeDesc.decidableOfWellFormedNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (subject classifier : RawTerm scope) :
    Decidable (HasTypeDesc profile context subject classifier) :=
  match HasTypeDesc.inferWithWitness wellFormed subject with
  | .inr subjectHasNoType => isFalse (subjectHasNoType classifier)
  | .inl ⟨principalType, principalTyped⟩ =>
      match IsTypeDesc.decidableOfWellFormed wellFormed classifier with
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

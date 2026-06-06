import FX1Poly.Typed.IsTypeDescRigidity
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.SigmaCodeShape

/-! # FX1Poly/Typed/IsTypeDescDecidable
    — native `Decidable (IsTypeDesc Γ T)` for the formation engine (HT-A4 bricks B1c + B1d, off old `HasType`)

The native formation type-hood judgment `IsTypeDesc Γ T = ∃ ℓ f, HasTypeDesc Γ T (universeCodeCell ℓ f)` is
DECIDABLE, by a structural recursion on `T`'s head generator — the `HasTypeDesc` twin of the bespoke
`IsType.decidableOfWellFormed` (`IsTypeDecidable.lean`, #303), built ENTIRELY from `HasTypeDesc` pieces over
`WfContextDesc` (no `HasType.toHasType` oracle, no old-engine `WfContext`).

This file assembles the decision from the shipped leaves (`IsTypeDescRigidity.lean`, bricks B1a/B1b):
`gen_universeCode` ⇒ always a type; `gen_var` ⇒ a type iff the lookup is a universe code; `gen_piTyCode` /
`gen_sigmaTyCode` ⇒ a type iff both children are types (codomain under the domain binder), by recursion;
any other head ⇒ never a type (`IsTypeDesc.not_of_rootGenerator`).

## The telescope-unpacking helpers (the B1c prerequisite)

The native former inversion `HasTypeDesc.inversionPiCode` returns a `DescTelescope` premise.  The decider's
refutation arms need the two CHILD typings at the CONCRETE `domainCode` / `codomainCode` (the generic
`DescTelescope.twoChildComponents` existentially repacks the children, losing that link).  So this file first
re-derives, keeping the children concrete:

* `HasTypeDesc.inversionPiCodeChildren` / `inversionSigmaCodeChildren` — a `piTyCodeCell domainCode
  codomainCode` typed by the formation engine has `domainCode : Type@(domainLevel, flag)` and `codomainCode :
  Type@(codomainLevel, flag)` (codomain under `Γ.cons domainCode`), at a SHARED `flag`.  Proved by destructing
  the `inversionPiCode` telescope over the concrete `binderShape domainCode codomainCode` child spine — the
  child index pins each `cons` head to the concrete child and refutes the `nil` arms definitionally (the same
  propext-clean discipline as `twoChildComponents`).

## Zero-axiom verification

The decision data carrier `decideWithWitness` recurses on `RawTerm.size` (the `size_lt_{pi,sigma}TyCodeCell_*`
bricks); each leaf is a shipped zero-axiom lemma, the `inl` witnesses are the formation constructors
(`universeFormation` / `var` / `hasTypeDesc_{pi,sigma}Formation_viaGenArm`), and the `inr` refutations compose
the native inversions + `HasTypeDesc.uniquenessNative` + universe-code rigidity (`universeCodeCell_inj_of_conv`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Concrete-children inversion for a Π-type code.**  A `piTyCodeCell domainCode codomainCode` typed by the
formation engine has its two children typed at universe codes — `domainCode` at `Type@(domainLevel, flag)` in
`context`, `codomainCode` at `Type@(codomainLevel, flag)` under the domain binder — at a SHARED `flag`.  Unlike
the generic `DescTelescope.twoChildComponents` (which existentially repacks the children), this keeps
`domainCode` / `codomainCode` concrete, as the decider's refutation arms require.

Destructs the `HasTypeDesc.inversionPiCode` telescope over the concrete `binderShape domainCode codomainCode`
spine: each `cons` head is pinned to the concrete child by the `RawTermChildren` index, and the closing `nil`
is forced, so the nested `cases` is propext-clean (same discipline as `twoChildComponents`). -/
theorem HasTypeDesc.inversionPiCodeChildren {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag)
        ∧ HasTypeDesc profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) := by
  obtain ⟨_levels, flag, telescope⟩ := HasTypeDesc.inversionPiCode typed
  cases telescope with
  | cons _context _head domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _context2 _head2 codomainLevel _restLevels2 _flag2 _rest2 codomainTyped _tailTelescope =>
          exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

/-- **Concrete-children inversion for a Σ-type code** — the Σ mirror of `inversionPiCodeChildren`, over
`HasTypeDesc.inversionSigmaCode` and the `sigmaTyCodeCell` spine.  Identical recipe; only the former changes. -/
theorem HasTypeDesc.inversionSigmaCodeChildren {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (sigmaTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag)
        ∧ HasTypeDesc profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) := by
  obtain ⟨_levels, flag, telescope⟩ := HasTypeDesc.inversionSigmaCode typed
  cases telescope with
  | cons _context _head domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _context2 _head2 codomainLevel _restLevels2 _flag2 _rest2 codomainTyped _tailTelescope =>
          exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

/-- **The data-returning core of native `Decidable (IsTypeDesc Γ T)`.**  Either a universe witness
(`Σ'`-packaged level + flag + `HasTypeDesc` derivation — `Type`-valued, so the flag is DATA the Π/Σ arm can
compare) or a proof the cell inhabits no universe.  `IsTypeDesc` is a `Prop` (`∃ ℓ f, …`) whose existential
flag cannot eliminate into the `Type`-valued decision; this `PSum` carries the flag explicitly.

Recurses on `RawTerm.size` (the `size_lt_{pi,sigma}TyCodeCell_*` bricks), threading `WfContextDesc.cons` for
the codomain.  The `inr` arms refute via the native `inversionPiCodeChildren` / `inversionSigmaCodeChildren`
(a typeable Π/Σ has typeable children at a shared flag) and, for a flag mismatch,
`HasTypeDesc.uniquenessNative` + `universeCodeCell_inj_of_conv` (a child's universe flag is
derivation-unique).  The `HasTypeDesc` twin of `IsType.decideWithWitness`, fully off the old engine. -/
def IsTypeDesc.decideWithWitness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (classifier : RawTerm scope) :
    PSum
      (Σ' (levelExpr : LevelExpr) (flag : UniverseFlag),
        HasTypeDesc profile context classifier (universeCodeCell levelExpr flag))
      (IsTypeDesc profile context classifier → False) :=
  match classifier with
  | .mkGen generator payload children =>
      if hUniverse : generator = Generator.gen_universeCode then by
        subst hUniverse
        have cellIsUniverseCode :
            (RawTerm.mkGen Generator.gen_universeCode payload children)
              = universeCodeCell payload.1 payload.2 := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact .inl ⟨payload.1.lsucc, payload.2, by
          rw [cellIsUniverseCode]
          exact HasTypeDesc.universeFormation context payload.1 payload.2⟩
      else if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have cellIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children) = variableCell payload := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact match hLookupCell : context.lookup payload with
          | .mkGen lookupGenerator lookupPayload lookupChildren =>
              if hLookupUniverse : lookupGenerator = Generator.gen_universeCode then by
                subst hLookupUniverse
                have lookupIsUniverseCode :
                    context.lookup payload
                      = universeCodeCell lookupPayload.1 lookupPayload.2 := by
                  rw [hLookupCell, RawTermChildren.eq_childNil lookupChildren]; rfl
                exact .inl ⟨lookupPayload.1, lookupPayload.2, by
                  rw [cellIsVariable, ← lookupIsUniverseCode]
                  exact HasTypeDesc.var context payload⟩
              else by
                exact .inr (by
                  rw [cellIsVariable]
                  intro isTypeVariable
                  have headIsUniverse :
                      RawTerm.headGenerator (context.lookup payload)
                        = Generator.gen_universeCode :=
                    (IsTypeDesc.variableCell_iff_lookupIsUniverseCode
                      wellFormed payload).mp isTypeVariable
                  rw [hLookupCell] at headIsUniverse
                  exact hLookupUniverse headIsUniverse)
      else if hPi : generator = Generator.gen_piTyCode then
        match generator, children, hPi with
        | .gen_piTyCode, .childCons domainCode (.childCons codomainCode .childNil), rfl =>
              match IsTypeDesc.decideWithWitness wellFormed domainCode with
              | .inr domainNotType =>
                  .inr fun isTypePi => by
                    obtain ⟨_piLevel, _piFlag, piTyped⟩ := isTypePi
                    obtain ⟨domainLevel, _codomainLevel, sharedFlag, domainTyped, _⟩ :=
                      HasTypeDesc.inversionPiCodeChildren piTyped
                    exact domainNotType ⟨domainLevel, sharedFlag, domainTyped⟩
              | .inl ⟨domainLevel, domainFlag, domainTyped⟩ =>
                  match IsTypeDesc.decideWithWitness
                      (WfContextDesc.cons wellFormed ⟨domainLevel, domainFlag, domainTyped⟩)
                      codomainCode with
                  | .inr codomainNotType =>
                      .inr fun isTypePi => by
                        obtain ⟨_piLevel, _piFlag, piTyped⟩ := isTypePi
                        obtain ⟨_domainLevel, codomainLevel, sharedFlag, _, codomainTyped⟩ :=
                          HasTypeDesc.inversionPiCodeChildren piTyped
                        exact codomainNotType ⟨codomainLevel, sharedFlag, codomainTyped⟩
                  | .inl ⟨codomainLevel, codomainFlag, codomainTyped⟩ =>
                      if hFlag : domainFlag = codomainFlag then by
                        subst hFlag
                        exact .inl
                          ⟨LevelExpr.lmax domainLevel codomainLevel, domainFlag,
                            hasTypeDesc_piFormation_viaGenArm context domainCode codomainCode
                              domainLevel codomainLevel domainFlag domainTyped codomainTyped⟩
                      else
                        .inr fun isTypePi => by
                          obtain ⟨_piLevel, _piFlag, piTyped⟩ := isTypePi
                          obtain ⟨_invDomainLevel, _invCodomainLevel, _invFlag,
                            invDomainTyped, invCodomainTyped⟩ :=
                            HasTypeDesc.inversionPiCodeChildren piTyped
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
                  .inr fun isTypeSigma => by
                    obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := isTypeSigma
                    obtain ⟨domainLevel, _codomainLevel, sharedFlag, domainTyped, _⟩ :=
                      HasTypeDesc.inversionSigmaCodeChildren sigmaTyped
                    exact domainNotType ⟨domainLevel, sharedFlag, domainTyped⟩
              | .inl ⟨domainLevel, domainFlag, domainTyped⟩ =>
                  match IsTypeDesc.decideWithWitness
                      (WfContextDesc.cons wellFormed ⟨domainLevel, domainFlag, domainTyped⟩)
                      codomainCode with
                  | .inr codomainNotType =>
                      .inr fun isTypeSigma => by
                        obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := isTypeSigma
                        obtain ⟨_domainLevel, codomainLevel, sharedFlag, _, codomainTyped⟩ :=
                          HasTypeDesc.inversionSigmaCodeChildren sigmaTyped
                        exact codomainNotType ⟨codomainLevel, sharedFlag, codomainTyped⟩
                  | .inl ⟨codomainLevel, codomainFlag, codomainTyped⟩ =>
                      if hFlag : domainFlag = codomainFlag then by
                        subst hFlag
                        exact .inl
                          ⟨LevelExpr.lmax domainLevel codomainLevel, domainFlag,
                            hasTypeDesc_sigmaFormation_viaGenArm context domainCode codomainCode
                              domainLevel codomainLevel domainFlag domainTyped codomainTyped⟩
                      else
                        .inr fun isTypeSigma => by
                          obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := isTypeSigma
                          obtain ⟨_invDomainLevel, _invCodomainLevel, _invFlag,
                            invDomainTyped, invCodomainTyped⟩ :=
                            HasTypeDesc.inversionSigmaCodeChildren sigmaTyped
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
      else by
        have notFormer : typingRuleDescOf generator = none := by
          cases hGen : typingRuleDescOf generator with
          | none => rfl
          | some rule =>
              rcases typingRuleDescOf_isPiOrSigma hGen with hIsPi | hIsSigma
              · exact absurd hIsPi hPi
              · exact absurd hIsSigma hSigma
        exact .inr (IsTypeDesc.not_of_rootGenerator hVariable hUniverse notFormer)
  termination_by classifier.size
  decreasing_by
    all_goals first
      | exact size_lt_piTyCodeCell_domain _ _
      | exact size_lt_piTyCodeCell_codomain _ _
      | exact size_lt_sigmaTyCodeCell_domain _ _
      | exact size_lt_sigmaTyCodeCell_codomain _ _

/-- **Native `Decidable (IsTypeDesc Γ T)`** (HT-A4 brick B1d) — decide whether `classifier` inhabits some
universe per the formation engine, off the old `HasType`.  A thin wrapper over the data-returning
`decideWithWitness`: a universe witness is the `isTrue` evidence; the `no-universe` proof is the `isFalse`
evidence.  The `HasTypeDesc` twin of `IsType.decidableOfWellFormed`, over `WfContextDesc`. -/
def IsTypeDesc.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (classifier : RawTerm scope) : Decidable (IsTypeDesc profile context classifier) :=
  match IsTypeDesc.decideWithWitness wellFormed classifier with
  | .inl ⟨levelExpr, flag, typed⟩ => isTrue ⟨levelExpr, flag, typed⟩
  | .inr notType => isFalse notType

end FX1Poly.Typed

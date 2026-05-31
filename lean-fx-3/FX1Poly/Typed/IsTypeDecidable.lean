import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeDecidableConv
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.SigmaCodeShape

/-! # FX1Poly/Typed/IsTypeDecidable
    — characterization of which cells are types (current fragment)

`IsType context classifier` unfolds to `∃ levelExpr flag, HasType context
classifier (universeCodeCell levelExpr flag)`.  On the current `HasType` fragment
this is decidable by casing on `classifier`'s head generator:

* `gen_universeCode` head ⇒ always a type (`IsType.ofUniverseCodeCell`, via
  `HasType.universeFormation`);
* `gen_var` head ⇒ a type *iff* the looked-up classifier is itself a universe
  code (`IsType.variableCell_iff_lookupIsUniverseCode`) — the only case that
  consults the context; forward by `inversionVariable` + normal-form rigidity
  (`Conv.eq_of_isType`), backward by the universe-code destructor + the variable
  rule;
* `gen_piTyCode` / `gen_sigmaTyCode` head ⇒ a type iff its domain and codomain
  children are types (the codomain under the domain binder), decided by recursing
  into `decideWithWitness`;
* any other head ⇒ never a type (`IsType.not_of_headGenerator`, via
  `typedSubjectIsVariableOrUniverseCode`).

These lemmas are the content of `Decidable IsType` (#303); the decision procedure
`decideWithWitness` assembles them by casing on the cell's head generator
(`DecidableEq Generator`) over the cell destructors in `UniverseCodeShape` /
`SigmaCodeShape`.

## Zero-axiom verification

The forward variable case rests on normal-form rigidity (`Conv.eq_of_isType`,
itself zero-axiom) rather than on any normalizer: both endpoints of the
`inversionVariable` convertibility are types, hence normal, so the
`Conv` collapses to a literal cell equality.  The refutation `subst`s the
cell-shape equality and closes by `rfl` at default transparency (a concrete
cell's head generator reduces definitionally).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Universe-code cells are always types: `universeFormation` classifies
`universeCodeCell levelExpr flag` by `universeCodeCell levelExpr.lsucc flag`.
(Named `ofUniverseCodeCell`, not `universeCodeCell`, so it does not shadow the
cell constructor inside other `IsType.`-prefixed theorem bodies.) -/
theorem IsType.ofUniverseCodeCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsType profile context (universeCodeCell levelExpr flag) :=
  ⟨levelExpr.lsucc, flag, HasType.universeFormation context levelExpr flag⟩

/-- A variable cell is a type exactly when its looked-up classifier is a universe
code.

Forward: `inversionVariable` yields `Conv (universeCodeCell levelExpr flag)
(context.lookup index)`; both endpoints are types (`IsType.universeCodeCell` and
`WfContext.lookupIsType`), so normal-form rigidity (`Conv.eq_of_isType`)
collapses the `Conv` to a cell equality, whence the looked-up head is
`gen_universeCode`.

Backward: the universe-code destructor rebuilds `context.lookup index =
universeCodeCell levelExpr flag`, and the variable rule types `variableCell
index` by exactly its looked-up classifier. -/
theorem IsType.variableCell_iff_lookupIsUniverseCode {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContext context) (index : Fin scope) :
    IsType profile context (variableCell index)
      ↔ RawTerm.headGenerator (context.lookup index) = Generator.gen_universeCode := by
  constructor
  · rintro ⟨levelExpr, flag, typed⟩
    have converts :
        Conv (universeCodeCell levelExpr flag) (context.lookup index) :=
      HasType.inversionVariable wellFormed typed
    have lookupIsType : IsType profile context (context.lookup index) :=
      WfContext.lookupIsType context wellFormed index
    have codeIsType : IsType profile context (universeCodeCell levelExpr flag) :=
      IsType.ofUniverseCodeCell levelExpr flag
    have cellsEqual :
        universeCodeCell levelExpr flag = context.lookup index :=
      Conv.eq_of_isType codeIsType lookupIsType converts
    rw [← cellsEqual]
    exact headGenerator_universeCodeCell levelExpr flag
  · intro lookupHead
    obtain ⟨levelExpr, flag, lookupEqualsCode⟩ :=
      eq_universeCodeCell_of_headGenerator lookupHead
    refine ⟨levelExpr, flag, ?_⟩
    rw [← lookupEqualsCode]
    exact HasType.var context index

/-- A cell whose head generator is neither `gen_var` nor `gen_universeCode` is
never a type: every typed subject is a variable or universe-code cell
(`typedSubjectIsVariableOrUniverseCode`), so no derivation can type this cell as
a universe code. -/
theorem IsType.not_of_headGenerator {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (notVariable : RawTerm.headGenerator classifier ≠ Generator.gen_var)
    (notUniverseCode :
      RawTerm.headGenerator classifier ≠ Generator.gen_universeCode)
    (notPi : RawTerm.headGenerator classifier ≠ Generator.gen_piTyCode)
    (notSigma : RawTerm.headGenerator classifier ≠ Generator.gen_sigmaTyCode) :
    ¬ IsType profile context classifier := by
  rintro ⟨levelExpr, flag, typed⟩
  rcases typed.typedSubjectIsVariableOrUniverseCode with
    ⟨index, subjectIsVariable⟩ | ⟨codeLevel, codeFlag, subjectIsUniverseCode⟩ |
      ⟨domainCode, codomainCode, subjectIsPi⟩ |
      ⟨domainCode, codomainCode, subjectIsSigma⟩
  · subst subjectIsVariable
    exact notVariable (headGenerator_variableCell index)
  · subst subjectIsUniverseCode
    exact notUniverseCode (headGenerator_universeCodeCell codeLevel codeFlag)
  · subst subjectIsPi
    exact notPi (headGenerator_piTyCodeCell domainCode codomainCode)
  · subst subjectIsSigma
    exact notSigma (headGenerator_sigmaTyCodeCell domainCode codomainCode)

/-- The DATA-returning core of `Decidable IsType`: either a universe witness
(`Σ'`-packaged level + flag + typing — `Type`-valued, so the flag is DATA the Π
arm can compare) or a proof the cell inhabits no universe.  `IsType` is a `Prop`
(`∃ level flag, …`), whose existential flag cannot be eliminated into the
`Type`-valued decision; this `PSum` carries the flag explicitly so the
`gen_piTyCode` arm can decide the shared-flag side condition.

Recurses into a Π's children (well-founded on `RawTerm.size` via the
`size_lt_piTyCodeCell_*` bricks), threading `WfContext.cons` for the codomain.
The `inr` arms refute: `inversionPiCode` forces a typeable Π's children typeable,
and a flag mismatch contradicts `uniqueness` (a child's universe flag is
derivation-unique). -/
def IsType.decideWithWitness {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (classifier : RawTerm scope) :
    PSum
      (Σ' (levelExpr : LevelExpr) (flag : UniverseFlag),
        HasType profile context classifier (universeCodeCell levelExpr flag))
      (IsType profile context classifier → False) :=
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
          exact HasType.universeFormation context payload.1 payload.2⟩
      else if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have cellIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children)
              = variableCell payload := by
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
                  exact HasType.var context payload⟩
              else by
                exact .inr (by
                  rw [cellIsVariable]
                  intro isTypeVariable
                  have headIsUniverse :
                      RawTerm.headGenerator (context.lookup payload)
                        = Generator.gen_universeCode :=
                    (IsType.variableCell_iff_lookupIsUniverseCode
                      wellFormed payload).mp isTypeVariable
                  rw [hLookupCell] at headIsUniverse
                  exact hLookupUniverse headIsUniverse)
      else if hPi : generator = Generator.gen_piTyCode then
        -- Match `generator` itself (NOT the `hPi` equation) against `gen_piTyCode`,
        -- so the matcher refines `children`'s type to the `[0,1]` spine — an
        -- Eq-discriminant does not refine sibling discriminants' types, but a
        -- value-discriminant does.  Matching `hPi` against `rfl` alongside prunes
        -- every other generator (`noConfusion`), giving exhaustiveness with one
        -- arm.  Crucially the refinement propagates into the `decreasing_by` goal
        -- too (unlike `subst hPi`, which splits the goal's `children` from the
        -- body's across the `RawTerm` / `RawTermChildren` mutual boundary).  This
        -- exposes the domain / codomain as DATA (an `Exists` could not eliminate
        -- into this `Type`-valued goal); recurse into each, then reconcile flags.
        match generator, children, hPi with
        | .gen_piTyCode, .childCons domainCode (.childCons codomainCode .childNil), rfl =>
              match IsType.decideWithWitness wellFormed domainCode with
              | .inr domainNotType =>
                  .inr fun isTypePi => by
                    obtain ⟨_piLevel, _piFlag, piTyped⟩ := isTypePi
                    obtain ⟨domainLevel, _codomainLevel, sharedFlag,
                      domainTyped, _, _⟩ := HasType.inversionPiCode wellFormed piTyped
                    exact domainNotType ⟨domainLevel, sharedFlag, domainTyped⟩
              | .inl ⟨domainLevel, domainFlag, domainTyped⟩ =>
                  match IsType.decideWithWitness
                      (WfContext.cons wellFormed
                        ⟨domainLevel, domainFlag, domainTyped⟩) codomainCode with
                  | .inr codomainNotType =>
                      .inr fun isTypePi => by
                        obtain ⟨_piLevel, _piFlag, piTyped⟩ := isTypePi
                        obtain ⟨_domainLevel, codomainLevel, sharedFlag,
                          _, codomainTyped, _⟩ :=
                          HasType.inversionPiCode wellFormed piTyped
                        exact codomainNotType ⟨codomainLevel, sharedFlag, codomainTyped⟩
                  | .inl ⟨codomainLevel, codomainFlag, codomainTyped⟩ =>
                      if hFlag : domainFlag = codomainFlag then by
                        subst hFlag
                        exact .inl
                          ⟨LevelExpr.lmax domainLevel codomainLevel, domainFlag,
                            HasType.piFormation context domainCode codomainCode
                              domainLevel codomainLevel domainFlag
                              domainTyped codomainTyped⟩
                      else
                        .inr fun isTypePi => by
                          obtain ⟨_piLevel, _piFlag, piTyped⟩ := isTypePi
                          obtain ⟨_invDomainLevel, _invCodomainLevel, _invFlag,
                            invDomainTyped, invCodomainTyped, _⟩ :=
                            HasType.inversionPiCode wellFormed piTyped
                          obtain ⟨_, domainFlagAgree⟩ :=
                            levelFlag_eq_of_conv_universeCodeCell
                              (context := context)
                              (HasType.uniqueness wellFormed
                                domainTyped invDomainTyped)
                          obtain ⟨_, codomainFlagAgree⟩ :=
                            levelFlag_eq_of_conv_universeCodeCell
                              (context := context.cons domainCode)
                              (HasType.uniqueness
                                (WfContext.cons wellFormed
                                  ⟨domainLevel, domainFlag, domainTyped⟩)
                                codomainTyped invCodomainTyped)
                          exact hFlag (domainFlagAgree.trans codomainFlagAgree.symm)
      else if hSigma : generator = Generator.gen_sigmaTyCode then
        -- exact mirror of the `gen_piTyCode` branch: value-discriminant match on
        -- `generator` refines `children` to the `[0,1]` spine, recurse into each
        -- child, reconcile flags.  Σ produces `Type@(lmax …)` just like Π, so the
        -- decision is structurally identical (`inversionSigmaCode`,
        -- `HasType.sigmaFormation`, the same `uniqueness` flag-agreement refutation).
        match generator, children, hSigma with
        | .gen_sigmaTyCode, .childCons domainCode (.childCons codomainCode .childNil), rfl =>
              match IsType.decideWithWitness wellFormed domainCode with
              | .inr domainNotType =>
                  .inr fun isTypeSigma => by
                    obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := isTypeSigma
                    obtain ⟨domainLevel, _codomainLevel, sharedFlag,
                      domainTyped, _, _⟩ := HasType.inversionSigmaCode wellFormed sigmaTyped
                    exact domainNotType ⟨domainLevel, sharedFlag, domainTyped⟩
              | .inl ⟨domainLevel, domainFlag, domainTyped⟩ =>
                  match IsType.decideWithWitness
                      (WfContext.cons wellFormed
                        ⟨domainLevel, domainFlag, domainTyped⟩) codomainCode with
                  | .inr codomainNotType =>
                      .inr fun isTypeSigma => by
                        obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := isTypeSigma
                        obtain ⟨_domainLevel, codomainLevel, sharedFlag,
                          _, codomainTyped, _⟩ :=
                          HasType.inversionSigmaCode wellFormed sigmaTyped
                        exact codomainNotType ⟨codomainLevel, sharedFlag, codomainTyped⟩
                  | .inl ⟨codomainLevel, codomainFlag, codomainTyped⟩ =>
                      if hFlag : domainFlag = codomainFlag then by
                        subst hFlag
                        exact .inl
                          ⟨LevelExpr.lmax domainLevel codomainLevel, domainFlag,
                            HasType.sigmaFormation context domainCode codomainCode
                              domainLevel codomainLevel domainFlag
                              domainTyped codomainTyped⟩
                      else
                        .inr fun isTypeSigma => by
                          obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := isTypeSigma
                          obtain ⟨_invDomainLevel, _invCodomainLevel, _invFlag,
                            invDomainTyped, invCodomainTyped, _⟩ :=
                            HasType.inversionSigmaCode wellFormed sigmaTyped
                          obtain ⟨_, domainFlagAgree⟩ :=
                            levelFlag_eq_of_conv_universeCodeCell
                              (context := context)
                              (HasType.uniqueness wellFormed
                                domainTyped invDomainTyped)
                          obtain ⟨_, codomainFlagAgree⟩ :=
                            levelFlag_eq_of_conv_universeCodeCell
                              (context := context.cons domainCode)
                              (HasType.uniqueness
                                (WfContext.cons wellFormed
                                  ⟨domainLevel, domainFlag, domainTyped⟩)
                                codomainTyped invCodomainTyped)
                          exact hFlag (domainFlagAgree.trans codomainFlagAgree.symm)
      else
        .inr (IsType.not_of_headGenerator hVariable hUniverse hPi hSigma)
  termination_by classifier.size
  decreasing_by
    -- four recursive calls now (domain + codomain for each of Π and Σ).  The
    -- value-discriminant matcher refinement keeps each goal's cell concrete
    -- (`piTyCodeCell` or `sigmaTyCodeCell`), so the matching `RawTerm.size` brick
    -- applies — a Nat measure because structural recursion cannot cross the
    -- `RawTerm` / `RawTermChildren` mutual boundary.  `first` dispatches each goal
    -- to whichever of the four bricks unifies.
    all_goals first
      | exact size_lt_piTyCodeCell_domain _ _
      | exact size_lt_piTyCodeCell_codomain _ _
      | exact size_lt_sigmaTyCodeCell_domain _ _
      | exact size_lt_sigmaTyCodeCell_codomain _ _

/-- Decide whether `classifier` inhabits some universe, for the current fragment
(var / conv / universe / Π-formation / Σ-formation).  A thin wrapper over the
data-returning `decideWithWitness`: a universe witness is the `isTrue` evidence;
the `no-universe` proof is the `isFalse` evidence. -/
def IsType.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (classifier : RawTerm scope) : Decidable (IsType profile context classifier) :=
  match IsType.decideWithWitness wellFormed classifier with
  | .inl ⟨levelExpr, flag, typed⟩ => isTrue ⟨levelExpr, flag, typed⟩
  | .inr notType => isFalse notType

end FX1Poly.Typed

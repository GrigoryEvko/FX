import FX1Poly.Typed.IsTypeDecidable

/-! # FX1Poly/Typed/HasTypeDecidable
    — typed checking collapses to classifier equality (current fragment)

On the current `HasType` fragment (`var` / `conv` / `universeFormation`), deciding
`HasType context subject classifier` does NOT require a `Conv` decision: validity
(`HasType.classifierIsType`) makes every classifier an `IsType`, hence a
non-stepping normal leaf, and the per-shape inversions hand back a `Conv` to
another normal cell — so normal-form rigidity (`Conv.eq_of_isType`) collapses the
whole judgment to *syntactic equality of the classifier*:

* `HasType context (variableCell i) classifier ↔ classifier = context.lookup i`
  (`HasType.variableCell_iff_classifierEqLookup`);
* `HasType context (universeCodeCell e f) classifier
   ↔ classifier = universeCodeCell e.lsucc f`
  (`HasType.universeCodeCell_iff_classifierEqSucc`);
* a subject whose head is neither `gen_var` nor `gen_universeCode` is never typed
  (`HasType.not_of_headGenerator`).

These are the full content of `Decidable (HasType …)` (#461) for this fragment —
the decision procedure then assembles them over `DecidableEq RawTerm`, with no
normalizer (the feared general-`Conv` / NbE dependency never arises, because a
non-type classifier is exactly the no-derivation case).

## Zero-axiom verification

Forward directions rest on `classifierIsType` + the inversions + rigidity
(`Conv.eq_of_isType`), all zero-axiom; backward directions `subst` the classifier
equality and apply the `var` / `universeFormation` rule.  The refutation reuses
`typedSubjectIsVariableOrUniverseCode` + the concrete-cell head computations.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- `variableCell index` is typed by exactly its looked-up classifier (and
nothing else): forward by `inversionVariable` + validity + rigidity, backward by
the `var` rule.  No `Conv` decision survives — both `classifier` (validity) and
`context.lookup index` (well-formedness) are normal, so the convertibility
becomes an equality. -/
theorem HasType.variableCell_iff_classifierEqLookup {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContext context) (index : Fin scope)
    (classifier : RawTerm scope) :
    HasType profile context (variableCell index) classifier
      ↔ classifier = context.lookup index := by
  constructor
  · intro typed
    have converts : Conv classifier (context.lookup index) :=
      HasType.inversionVariable wellFormed typed
    have classifierIsType : IsType profile context classifier :=
      HasType.classifierIsType wellFormed typed
    have lookupIsType : IsType profile context (context.lookup index) :=
      WfContext.lookupIsType context wellFormed index
    exact Conv.eq_of_isType classifierIsType lookupIsType converts
  · intro classifierEqualsLookup
    subst classifierEqualsLookup
    exact HasType.var context index

/-- A universe-code cell `universeCodeCell e flag` is typed by exactly the next
universe `universeCodeCell e.lsucc flag` (and nothing else): forward by
`inversionUniverseCode` + validity + rigidity, backward by `universeFormation`. -/
theorem HasType.universeCodeCell_iff_classifierEqSucc {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    (wellFormed : WfContext context) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (classifier : RawTerm scope) :
    HasType profile context (universeCodeCell levelExpr flag) classifier
      ↔ classifier = universeCodeCell levelExpr.lsucc flag := by
  constructor
  · intro typed
    have converts :
        Conv classifier (universeCodeCell levelExpr.lsucc flag) :=
      HasType.inversionUniverseCode wellFormed typed
    have classifierIsType : IsType profile context classifier :=
      HasType.classifierIsType wellFormed typed
    have succIsType :
        IsType profile context (universeCodeCell levelExpr.lsucc flag) :=
      IsType.ofUniverseCodeCell levelExpr.lsucc flag
    exact Conv.eq_of_isType classifierIsType succIsType converts
  · intro classifierEqualsSucc
    subst classifierEqualsSucc
    exact HasType.universeFormation context levelExpr flag

/-- A subject whose head generator is none of `gen_var`, `gen_universeCode`, or
`gen_piTyCode` has no typing derivation under any classifier: every typed subject
is a variable, universe-code, or Π-type-code cell
(`typedSubjectIsVariableOrUniverseCode`, the 3-way classification). -/
theorem HasType.not_of_headGenerator {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (notVariable : RawTerm.headGenerator subject ≠ Generator.gen_var)
    (notUniverseCode :
      RawTerm.headGenerator subject ≠ Generator.gen_universeCode)
    (notPi : RawTerm.headGenerator subject ≠ Generator.gen_piTyCode) :
    ¬ HasType profile context subject classifier := by
  intro typed
  rcases typed.typedSubjectIsVariableOrUniverseCode with
    ⟨index, subjectIsVariable⟩ | ⟨codeLevel, codeFlag, subjectIsUniverseCode⟩ |
      ⟨domainCode, codomainCode, subjectIsPi⟩
  · subst subjectIsVariable
    exact notVariable (headGenerator_variableCell index)
  · subst subjectIsUniverseCode
    exact notUniverseCode (headGenerator_universeCodeCell codeLevel codeFlag)
  · subst subjectIsPi
    exact notPi (headGenerator_piTyCodeCell domainCode codomainCode)

/-- Decide `HasType context subject classifier` for the current fragment — typed
checking as a decision procedure.  A direct mirror of
`IsType.decidableOfWellFormed`: case on the SUBJECT cell `mkGen generator payload
children` (single ctor → large elimination into `Decidable`; `payload` carries
the index / `(level, flag)` as data), then `dite` on `generator` via
`DecidableEq Generator` (`dite`, never `by_cases` — `Classical`):

* `gen_universeCode` → decide `classifier = universeCodeCell payload.1.lsucc
  payload.2` (`DecidableEq RawTerm`) via `universeCodeCell_iff_classifierEqSucc`;
* `gen_var` → decide `classifier = context.lookup payload` via
  `variableCell_iff_classifierEqLookup`;
* otherwise → `isFalse` via `HasType.not_of_headGenerator`.

No `Conv` decision / normalizer: the iff lemmas already collapsed typed checking
to classifier equality.  Each cell-shape collapse (`mkGen … = universeCodeCell /
variableCell` via `eq_childNil`) is `rw`-rewritten on the `HasType` Prop goal
inside `isTrue` / `isFalse`, never the `Decidable` goal. -/
def HasType.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (subject classifier : RawTerm scope) :
    Decidable (HasType profile context subject classifier) :=
  match subject with
  | .mkGen generator payload children =>
      if hUniverse : generator = Generator.gen_universeCode then by
        subst hUniverse
        have subjectIsUniverseCode :
            (RawTerm.mkGen Generator.gen_universeCode payload children)
              = universeCodeCell payload.1 payload.2 := by
          rw [RawTermChildren.eq_childNil children]
          rfl
        exact
          if hClassifierIsSucc :
              classifier = universeCodeCell payload.1.lsucc payload.2 then
            isTrue (by
              rw [subjectIsUniverseCode]
              exact (HasType.universeCodeCell_iff_classifierEqSucc
                wellFormed payload.1 payload.2 classifier).mpr hClassifierIsSucc)
          else
            isFalse (by
              rw [subjectIsUniverseCode]
              exact fun typed =>
                hClassifierIsSucc
                  ((HasType.universeCodeCell_iff_classifierEqSucc
                    wellFormed payload.1 payload.2 classifier).mp typed))
      else if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have subjectIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children)
              = variableCell payload := by
          rw [RawTermChildren.eq_childNil children]
          rfl
        exact
          if hClassifierIsLookup : classifier = context.lookup payload then
            isTrue (by
              rw [subjectIsVariable]
              exact (HasType.variableCell_iff_classifierEqLookup
                wellFormed payload classifier).mpr hClassifierIsLookup)
          else
            isFalse (by
              rw [subjectIsVariable]
              exact fun typed =>
                hClassifierIsLookup
                  ((HasType.variableCell_iff_classifierEqLookup
                    wellFormed payload classifier).mp typed))
      else if hPi : generator = Generator.gen_piTyCode then
        -- Π subject: unlike `var` / `universe`, a Π's classifier is not a fixed
        -- function of the subject — it is `Type@(lmax domainLevel codomainLevel,
        -- flag)`, with the levels / flag determined by the children's typings.  So
        -- route through `IsType.decideWithWitness` (value-discriminant match on
        -- `generator` exposes the `[0,1]` spine, refining into the `decideWithWitness`
        -- call): it returns the PRINCIPAL universe witness `piTyped` (or refutes any
        -- typehood).  Typed checking then collapses to classifier equality against
        -- that principal universe — `uniqueness` + rigidity (`Conv.eq_of_isType`),
        -- exactly as the `var` / `universe` arms, no `Conv` decision surviving.
        match generator, children, hPi with
        | .gen_piTyCode, .childCons domainCode (.childCons codomainCode .childNil), rfl =>
            match IsType.decideWithWitness wellFormed
                (piTyCodeCell domainCode codomainCode) with
            | .inl ⟨principalLevel, principalFlag, piTyped⟩ =>
                if hClassifierIsPrincipal :
                    classifier = universeCodeCell principalLevel principalFlag then
                  isTrue (by subst hClassifierIsPrincipal; exact piTyped)
                else
                  isFalse (fun typed => by
                    -- a second classifier converts to the principal one (uniqueness);
                    -- both are types, so rigidity forces syntactic equality
                    exact hClassifierIsPrincipal (Conv.eq_of_isType
                      (HasType.classifierIsType wellFormed typed)
                      (IsType.ofUniverseCodeCell principalLevel principalFlag)
                      (HasType.uniqueness wellFormed typed piTyped)))
            | .inr piNotType =>
                isFalse (fun typed => by
                  -- a typed Π IS a type (its children inhabit universes), which
                  -- `piNotType` rules out
                  obtain ⟨domainLevel, codomainLevel, sharedFlag,
                    domainTyped, codomainTyped, _⟩ :=
                    HasType.inversionPiCode wellFormed typed
                  exact piNotType
                    ⟨LevelExpr.lmax domainLevel codomainLevel, sharedFlag,
                      HasType.piFormation context domainCode codomainCode
                        domainLevel codomainLevel sharedFlag
                        domainTyped codomainTyped⟩)
      else
        isFalse (HasType.not_of_headGenerator hVariable hUniverse hPi)

/-- Decidable typed conversion (★ A-core, #462): the convertibility of the
CLASSIFIERS of two well-typed terms is decidable.  Both classifiers are `IsType`
by validity (`HasType.classifierIsType`), hence normal leaves, so this reduces to
`Conv.decidableOfIsType` (normal-form rigidity + `DecidableEq RawTerm`, no
normalizer).  This is the entry point a bidirectional checker uses to compare a
synthesized classifier against an expected one — the typed-Conv leg of the
leaf-fragment decidable-typing triad. -/
def Conv.decidableOfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstSubject firstClassifier secondSubject secondClassifier : RawTerm scope}
    (wellFormed : WfContext context)
    (firstTyped : HasType profile context firstSubject firstClassifier)
    (secondTyped : HasType profile context secondSubject secondClassifier) :
    Decidable (Conv firstClassifier secondClassifier) :=
  Conv.decidableOfIsType
    (HasType.classifierIsType wellFormed firstTyped)
    (HasType.classifierIsType wellFormed secondTyped)

end FX1Poly.Typed

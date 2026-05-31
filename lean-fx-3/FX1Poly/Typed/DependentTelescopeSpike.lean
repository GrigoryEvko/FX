import FX1Poly.Typed.HasTypeGen

/-! # SPIKE: generic variadic dependent-telescope typed-children spine.
Research only — validates/refutes the description-universe pivot.

KEY INSIGHT (avoids the shift-rebasing wall): index the CHILDREN by a fixed
`baseScope`, and let only the CONTEXT grow, tracked by `currentDepth`.  The head
child at each step sits at `baseScope + currentDepth` (so its absolute shift in
the `RawTermChildren` list equals the depth), typed in a context at the same
scope.  The recursion extends the context (`context.cons head`, scope
`(baseScope+currentDepth)+1`) and increments depth — and
`(baseScope+currentDepth)+1` is DEFINITIONALLY `baseScope+(currentDepth+1)`, so
no cast is needed and the children never re-base.  The spine thereby accepts
EXACTLY cumulative `[0,1,…,n-1]` telescopes (a flat `[0,0]` cannot fire `cons`
past depth 0 — correct, that's a different shape). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Generic variadic dependent-telescope spine: each child is a type at its level
in the context extended by all PRIOR children.  Standalone (references the
already-defined `HasTypeGen` positively in `cons`; no mutual block needed). -/
inductive DependentTelescopeChildren (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      DependentTelescopeChildren profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasTypeGen profile context head (universeCodeCell headLevel flag))
      (restTyped :
        DependentTelescopeChildren profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      DependentTelescopeChildren profile context (headLevel :: restLevels) flag
        (.childCons head rest)

/-- Faithfulness: the `[0,1]` instance reconstructs exactly what s1's fixed
`DependentBinaryFormationChildren` accepted (domain typed in `context`, codomain
typed under the domain binder), over `RawTermChildren.binderShape`. -/
theorem dependentTelescope_reconstructs_piFormation
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeGen profile context domain (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeGen profile (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    DependentTelescopeChildren profile (currentDepth := 0) context
      [domainLevel, codomainLevel] flag
      (RawTermChildren.binderShape domain codomain) := by
  refine DependentTelescopeChildren.cons (currentDepth := 0) context domain
    domainLevel [codomainLevel] flag (.childCons codomain .childNil)
    domainTyped ?_
  exact DependentTelescopeChildren.cons (currentDepth := 1) (context.cons domain)
    codomain codomainLevel [] flag .childNil codomainTyped
    (DependentTelescopeChildren.nil (currentDepth := 2) (context.cons domain |>.cons codomain) flag)

/-- Genuine variadicity: a 3-ary `[0,1,2]` cumulative telescope (NOT secretly
binary).  Each child typed under all priors; the spine accepts it. -/
theorem dependentTelescope_threeAry
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (childZero : RawTerm (scope + 0)) (childOne : RawTerm (scope + 1))
    (childTwo : RawTerm (scope + 2))
    (levelZero levelOne levelTwo : LevelExpr) (flag : UniverseFlag)
    (typedZero :
      HasTypeGen profile context childZero (universeCodeCell levelZero flag))
    (typedOne :
      HasTypeGen profile (context.cons childZero) childOne
        (universeCodeCell levelOne flag))
    (typedTwo :
      HasTypeGen profile ((context.cons childZero).cons childOne) childTwo
        (universeCodeCell levelTwo flag)) :
    DependentTelescopeChildren profile (currentDepth := 0) context
      [levelZero, levelOne, levelTwo] flag
      (.childCons childZero (.childCons childOne (.childCons childTwo .childNil))) := by
  refine DependentTelescopeChildren.cons (currentDepth := 0) context childZero
    levelZero [levelOne, levelTwo] flag
    (.childCons childOne (.childCons childTwo .childNil)) typedZero ?_
  refine DependentTelescopeChildren.cons (currentDepth := 1) (context.cons childZero)
    childOne levelOne [levelTwo] flag (.childCons childTwo .childNil) typedOne ?_
  exact DependentTelescopeChildren.cons (currentDepth := 2)
    ((context.cons childZero).cons childOne) childTwo levelTwo [] flag
    .childNil typedTwo
    (DependentTelescopeChildren.nil (currentDepth := 3)
      (((context.cons childZero).cons childOne).cons childTwo) flag)

/-! ## MAXIMAL GENERALIZATION — arbitrary per-child classifiers

`DependentTelescopeChildren` above is variadic in arity but fixes every child to
a TYPE (classifier `universeCodeCell levelᵢ flag`), so it only expresses
telescopes of types (the formation shape).  The maximally-general typed-children
spine drops that constraint: each child is typed at an ARBITRARY classifier
`RawTerm (baseScope + currentDepth)` provided per `cons` step, which may mention
all prior children (it lives at the extended scope).  This is a genuine
dependent telescope of typed TERMS — exactly the `premisesHold` shape a
description-universe needs for eliminators (whose children are terms classified
by motive-dependent types, NOT universes).  The universe telescope is the
instance where every classifier is a `universeCodeCell`.  Same shift-rebasing
discipline (fixed `baseScope`, growing `currentDepth`, definitional
`(baseScope+currentDepth)+1 = baseScope+(currentDepth+1)`). -/
inductive DependentTelescopeTyped (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth)) :
      DependentTelescopeTyped profile context .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headClassifier : RawTerm (baseScope + currentDepth))
      (rest : RawTermChildren restShifts baseScope)
      (headTyped : HasTypeGen profile context head headClassifier)
      (restTyped :
        DependentTelescopeTyped profile (currentDepth := currentDepth + 1)
          (context.cons head) rest) :
      DependentTelescopeTyped profile context (.childCons head rest)

/-- The universe-code telescope is an INSTANCE of the general spine: the
`[0,1]` formation telescope (both children typed at universe codes) is accepted
by `DependentTelescopeTyped` with the classifiers chosen to be universe codes. -/
theorem dependentTelescopeTyped_reconstructs_piFormation
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeGen profile context domain (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeGen profile (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    DependentTelescopeTyped profile (currentDepth := 0) context
      (RawTermChildren.binderShape domain codomain) := by
  refine DependentTelescopeTyped.cons (currentDepth := 0) context domain
    (universeCodeCell domainLevel flag) (.childCons codomain .childNil)
    domainTyped ?_
  exact DependentTelescopeTyped.cons (currentDepth := 1) (context.cons domain)
    codomain (universeCodeCell codomainLevel flag) .childNil codomainTyped
    (DependentTelescopeTyped.nil (currentDepth := 2) (context.cons domain |>.cons codomain))

/-- Genuine generality beyond the universe telescope: a HETEROGENEOUS `[0,1]`
telescope whose children are typed at ARBITRARY classifiers (not universe
codes), each possibly depending on prior children.  This is the shape a
description-universe eliminator rule consumes — the universe-only spine cannot
express it, but the general spine accepts it. -/
theorem dependentTelescopeTyped_heterogeneous
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (childZero : RawTerm scope) (classifierZero : RawTerm scope)
    (childOne : RawTerm (scope + 1)) (classifierOne : RawTerm (scope + 1))
    (typedZero : HasTypeGen profile context childZero classifierZero)
    (typedOne :
      HasTypeGen profile (context.cons childZero) childOne classifierOne) :
    DependentTelescopeTyped profile (currentDepth := 0) context
      (RawTermChildren.binderShape childZero childOne) := by
  refine DependentTelescopeTyped.cons (currentDepth := 0) context childZero
    classifierZero (.childCons childOne .childNil) typedZero ?_
  exact DependentTelescopeTyped.cons (currentDepth := 1) (context.cons childZero)
    childOne classifierOne .childNil typedOne
    (DependentTelescopeTyped.nil (currentDepth := 2)
      (context.cons childZero |>.cons childOne))

end FX1Poly.Typed

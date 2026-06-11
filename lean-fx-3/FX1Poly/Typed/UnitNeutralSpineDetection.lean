import FX1Poly.Typed.UnitCollapseNeutralBoundary

/-! # FX1Poly/Typed/UnitNeutralSpineDetection
   — UNCONDITIONALLY sound spine-inversion detection of unit-typed neutrals (ULC-5 brick 1)

The compound-neutral verdict reduced the congruent unit-η decider's completeness to detecting
`typed-at-unitTypeCell` at neutral replacement sites.  The route decision (weighed per the ULC-5
plan): NOT the whnf-directed checker (the STR-5 hazard — an unsound positive would break collapse
SOUNDNESS) but SPINE INVERSION — synthesize the type of a variable-headed application spine by
walking it:

  * a VARIABLE synthesizes its context lookup (the `var` rule, sound in any context);
  * an APPLICATION synthesizes `subst0 codomain argument` when the function synthesizes a
    LITERAL Π code and the argument synthesizes exactly its domain (the `piElim` rule).

Every positive answer carries a real derivation — `detectSpineType_sound` is UNCONDITIONAL (no
wf, no route-H fragment): the only rules used are `var` and `piElim`, which need neither.

## The covered fragment, honestly

Variable-headed spines whose arguments are themselves such spines, with SYNTACTIC type matches
(no `Conv` at domains, no whnf of the function type).  This covers the compound-neutral witness
`app(f, x)` — `detectsCompoundUnitNeutral` computes its type to `unitTypeCell` by `rfl`, and
`compoundNeutralPair_certified` re-derives the boundary pair's congruent equality from the
DETECTOR's output alone.  Remaining undetected (the residual): λ-headed or value arguments
(checking them IS the general checking problem), `Conv`-but-not-equal domain matches, and
reducible function types.  Each future widening only strengthens the same soundness statement.

## Zero-axiom verification

Generator dispatch follows the `fireRootEtaRedex?` recipe — a single-ctor `.mkGen` match, `dite`
on generator equality, `▸`-transported children matched at their concrete index (a literal
generator pattern with a 203-ctor wildcard leaks `propext` through the match compiler).  The
recursion is STRUCTURAL ON A FUEL `Nat` (decremented at every call) so it both avoids
`WellFounded.fix` (which leaks `propext`+`Quot.sound` and blocks `rfl`) and computes by `rfl` on
concrete spines; soundness holds for EVERY fuel.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- Destructure a LITERAL Π code into its domain and codomain (syntactic — no whnf). -/
def asPiCode? {scope : Nat} : RawTerm scope → Option (RawTerm scope × RawTerm (scope + 1))
  | .mkGen generator _payload children =>
      if isPiCode : generator = Generator.gen_piTyCode then
        match (isPiCode ▸ children :
            RawTermChildren (Generator.gen_piTyCode.binderShifts) scope) with
        | .childCons domainCode (.childCons codomainCode .childNil) =>
            some (domainCode, codomainCode)
      else none

/-- `asPiCode?` is honest: a positive answer reconstructs the Π code. -/
theorem asPiCode?_sound {scope : Nat} {classifier : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (isPiCode : asPiCode? classifier = some (domainCode, codomainCode)) :
    classifier = piTyCodeCell domainCode codomainCode := by
  match classifier, isPiCode with
  | .mkGen generator payload children, isPiCode =>
    dsimp only [asPiCode?] at isPiCode
    split at isPiCode
    · next isPi =>
        subst isPi
        split at isPiCode
        next headDomain headCodomain childrenEq =>
        have childrenShape :
            children = .childCons headDomain (.childCons headCodomain .childNil) := childrenEq
        subst childrenShape
        cases Option.some.inj isPiCode
        rfl
    · cases isPiCode

/-- **Spine-inversion type synthesis**: walk a variable-headed application spine, synthesizing
the variable's lookup at the head and the `piElim` codomain instance at each application —
provided the function synthesizes a literal Π code and the argument synthesizes EXACTLY its
domain.  Fuel-structural (decremented at every recursive call); `none` at fuel 0. -/
def detectSpineType {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : Nat → RawTerm scope → Option (RawTerm scope)
  | 0, _ => none
  | fuel + 1, .mkGen generator payload children =>
      if isVariable : generator = Generator.gen_var then
        some (context.lookup (isVariable ▸ payload : Generator.gen_var.payload scope))
      else if isApp : generator = Generator.gen_app then
        match (isApp ▸ children :
            RawTermChildren (Generator.gen_app.binderShifts) scope) with
        | .childCons functionTerm (.childCons argument .childNil) =>
            match detectSpineType context fuel functionTerm with
            | some functionType =>
                match asPiCode? functionType with
                | some (domainCode, codomainCode) =>
                    match detectSpineType context fuel argument with
                    | some argumentType =>
                        if argumentType = domainCode then
                          some (RawTerm.subst0 codomainCode argument)
                        else none
                    | none => none
                | none => none
            | none => none
      else none

/-- **★ Spine detection is UNCONDITIONALLY sound**: every positive answer (at any fuel) is a
grown typing — the head by the `var` rule, each application by `piElim` — in ANY context, no
well-formedness.  This is the neutral-site detection the compound-neutral verdict demanded, with
no checker and no route-H hypothesis. -/
theorem detectSpineType_sound {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    (fuel : Nat) → (term : RawTerm scope) → {classifier : RawTerm scope} →
      detectSpineType context fuel term = some classifier →
      HasTypeDescPi profile context term classifier
  | 0, term, _, detectEq => by
      dsimp only [detectSpineType] at detectEq
      cases detectEq
  | fuel + 1, .mkGen generator payload children, classifier, detectEq => by
      dsimp only [detectSpineType] at detectEq
      split at detectEq
      · next isVariable =>
          subst isVariable
          cases Option.some.inj detectEq
          rw [RawTermChildren.eq_childNil children]
          exact HasTypeDescPi.ofFormation (HasTypeDesc.var context payload)
      · next notVariable =>
          split at detectEq
          · next isApp =>
              subst isApp
              split at detectEq
              next functionTerm argument childrenEq =>
              have childrenShape :
                  children = .childCons functionTerm (.childCons argument .childNil) :=
                childrenEq
              subst childrenShape
              split at detectEq
              · next functionType functionDetected =>
                  split at detectEq
                  · next domainCode codomainCode piCodeFound =>
                      split at detectEq
                      · next argumentType argumentDetected =>
                          split at detectEq
                          · next domainsMatch =>
                              cases Option.some.inj detectEq
                              exact HasTypeDescPi.piElim
                                (asPiCode?_sound piCodeFound ▸
                                  detectSpineType_sound context fuel
                                    functionTerm functionDetected)
                                (domainsMatch ▸
                                  detectSpineType_sound context fuel
                                    argument argumentDetected)
                          · cases detectEq
                      · cases detectEq
                  · cases detectEq
              · cases detectEq
          · cases detectEq

/-- **★ The compound-neutral witness IS detected**: the detector synthesizes `unitTypeCell` for
`app(f, x)` in `(f : Π(_:Unit).Unit, x : Unit)` — by `rfl` at fuel 2. -/
theorem detectsCompoundUnitNeutral (profile : PolyProfile) :
    detectSpineType (unitFunctionContext profile) 2 compoundUnitNeutral
      = some unitTypeCell := rfl

/-- **A decidable, unconditionally sound unit-η certificate at neutral sites**: two terms whose
spine-synthesized types are BOTH `unitTypeCell` (at any fuels) are congruently unit-η-equal —
`unitEta` fed by the detector's soundness on both sides. -/
theorem DefEqUnitEtaCong.ofDetectedUnitSpines {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    {leftFuel rightFuel : Nat}
    (leftDetected : detectSpineType context leftFuel leftTerm = some unitTypeCell)
    (rightDetected : detectSpineType context rightFuel rightTerm = some unitTypeCell) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .ofDefEq (.unitEta
    (Or.inr (detectSpineType_sound context leftFuel leftTerm leftDetected))
    (Or.inr (detectSpineType_sound context rightFuel rightTerm rightDetected)))

/-- **★ The boundary pair, certified by COMPUTATION**: the congruent equality of `x` and
`app(f, x)` — previously hand-derived — now follows from two `rfl` detector runs. -/
theorem compoundNeutralPair_certified (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      (variableCell ⟨0, Nat.le.step Nat.le.refl⟩) compoundUnitNeutral :=
  DefEqUnitEtaCong.ofDetectedUnitSpines (leftFuel := 1) rfl
    (detectsCompoundUnitNeutral profile)

end FX1Poly.Typed

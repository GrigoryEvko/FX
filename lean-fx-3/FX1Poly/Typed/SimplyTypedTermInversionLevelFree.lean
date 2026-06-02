import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree

/-! # FX1Poly/Typed/SimplyTypedTermInversionLevelFree
    — generation (inversion) lemmas for the simply-typed term judgment.

`SimplyTypedTermLF` is the well-scoped simply-typed lambda calculus over a context: `var`, `app`, `lam`,
with NO conversion arm.  That tightness is the point of these inversions: because typing is syntax-directed
(one rule per term shape, no subsumption), a term's type is determined EXACTLY by its shape, so the inversion
lemmas conclude EQUALITIES rather than the convertibilities the dependent `HasType` layer's inversions must
settle for.

* `SimplyTypedTermLF.inversionVariable` — a variable's type IS its context lookup.
* `SimplyTypedTermLF.inversionApplication` — an application's type is the function's arrow codomain, with the
  function typed at `Π domainCode. weaken classifier` and the argument at `domainCode`.
* `SimplyTypedTermLF.inversionLambda` — a lambda's type is `Π domainCode. weaken codomainBase` with the body
  typed in the extended context `context.cons domainCode` and both domain/codomain reducible type
  expressions.

These are the "extract the premises" step of subject reduction: SR-β inverts an `appCell (lamCell body) arg`
through `inversionApplication` then `inversionLambda` to recover the body's typing and the argument's typing,
which the substitution lemma then recombines into the typing of `subst0 arg body`.  (The substitution lemma
and SR-β itself are downstream; this file ships only the generation lemmas they consume.)

## Proof technique

The lean-fx-3 cell-index inversion recipe (see the typed-layer memory): a direct `cases`/`induction` on a
`SimplyTypedTermLF` derivation whose term index is a concrete `mkGen` cell leaks `propext`, so each lemma
generalizes the subject to a fresh variable threaded with a `subject = cell` equation
(`suffices general : … subject = cell → …`), inducts on the now-free-index derivation, discharges the
non-matching arms by `congrArg RawTerm.headGenerator` + `Generator.noConfusion` (the generator tags differ),
and extracts the matching arm's children by `injection` (the `mkGen` and `childCons` injections each expose
scope/shift index equalities ahead of the payload/child equalities — discarded with `_` placeholders).

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per
declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Inversion for a variable cell.**  `SimplyTypedTermLF` has no conversion arm, so a variable's type is
EXACTLY its context lookup. -/
theorem SimplyTypedTermLF.inversionVariable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {index : Fin scope} {classifier : RawTerm scope}
    (typed : SimplyTypedTermLF context (variableCell index) classifier) :
    classifier = context.lookup index := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reached : RawTerm generalScope},
        SimplyTypedTermLF generalContext subject reached →
          ∀ {targetIndex : Fin generalScope},
            subject = variableCell targetIndex →
              reached = generalContext.lookup targetIndex from
    general typed rfl
  intro generalScope generalContext subject reached derivation
  induction derivation with
  | var armIndex =>
      intro targetIndex subjectEq
      have indicesAgree : armIndex = targetIndex := by injection subjectEq
      subst indicesAgree; rfl
  | app functionTyped argumentTyped _ihFunction _ihArgument =>
      intro targetIndex subjectEq
      exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  | lam domainExpr codomainExpr bodyTyped _ihBody =>
      intro targetIndex subjectEq
      exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)

/-- **Inversion for an application cell.**  An application's type is the function's arrow codomain, with the
function typed at `Π domainCode. weaken classifier` and the argument at `domainCode`. -/
theorem SimplyTypedTermLF.inversionApplication {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument : RawTerm scope}
    {classifier : RawTerm scope}
    (typed : SimplyTypedTermLF context (appCell functionTerm argument) classifier) :
    ∃ domainCode : RawTerm scope,
      SimplyTypedTermLF context functionTerm (piTyCodeCell domainCode (RawTerm.weaken classifier)) ∧
        SimplyTypedTermLF context argument domainCode := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reached : RawTerm generalScope},
        SimplyTypedTermLF generalContext subject reached →
          ∀ {generalFunction generalArgument : RawTerm generalScope},
            subject = appCell generalFunction generalArgument →
              ∃ domainCode : RawTerm generalScope,
                SimplyTypedTermLF generalContext generalFunction
                    (piTyCodeCell domainCode (RawTerm.weaken reached)) ∧
                  SimplyTypedTermLF generalContext generalArgument domainCode from
    general typed rfl
  intro generalScope generalContext subject reached derivation
  induction derivation with
  | var armIndex =>
      intro generalFunction generalArgument subjectEq
      exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  | app functionTyped argumentTyped _ihFunction _ihArgument =>
      intro generalFunction generalArgument subjectEq
      injection subjectEq with _ _ _ childrenSpineEq
      injection childrenSpineEq with _ _ _ functionEq tailSpineEq
      injection tailSpineEq with _ _ _ argumentEq _
      subst functionEq; subst argumentEq
      exact ⟨_, functionTyped, argumentTyped⟩
  | lam domainExpr codomainExpr bodyTyped _ihBody =>
      intro generalFunction generalArgument subjectEq
      exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)

/-- **Inversion for a lambda cell.**  A lambda's type is `Π domainCode. weaken codomainBase`, with the body
typed in the extended context and both domain and codomain reducible type expressions. -/
theorem SimplyTypedTermLF.inversionLambda {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : SimplyTypedTermLF context (lamCell body) classifier) :
    ∃ domainCode codomainBase : RawTerm scope,
      classifier = piTyCodeCell domainCode (RawTerm.weaken codomainBase) ∧
        IsReducibleTypeExprLF domainCode ∧ IsReducibleTypeExprLF codomainBase ∧
          SimplyTypedTermLF (context.cons domainCode) body (RawTerm.weaken codomainBase) := by
  suffices general :
      ∀ {generalScope : Nat} {generalContext : TypingContext profile generalScope}
        {subject reached : RawTerm generalScope},
        SimplyTypedTermLF generalContext subject reached →
          ∀ {generalBody : RawTerm (generalScope + 1)},
            subject = lamCell generalBody →
              ∃ domainCode codomainBase : RawTerm generalScope,
                reached = piTyCodeCell domainCode (RawTerm.weaken codomainBase) ∧
                  IsReducibleTypeExprLF domainCode ∧ IsReducibleTypeExprLF codomainBase ∧
                    SimplyTypedTermLF (generalContext.cons domainCode) generalBody
                      (RawTerm.weaken codomainBase) from
    general typed rfl
  intro generalScope generalContext subject reached derivation
  induction derivation with
  | var armIndex =>
      intro generalBody subjectEq
      exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  | app functionTyped argumentTyped _ihFunction _ihArgument =>
      intro generalBody subjectEq
      exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  | lam domainExpr codomainExpr bodyTyped _ihBody =>
      intro generalBody subjectEq
      injection subjectEq with _ _ _ childrenSpineEq
      injection childrenSpineEq with _ _ _ bodyEq _
      subst bodyEq
      exact ⟨_, _, rfl, domainExpr, codomainExpr, bodyTyped⟩

end FX1Poly.Typed

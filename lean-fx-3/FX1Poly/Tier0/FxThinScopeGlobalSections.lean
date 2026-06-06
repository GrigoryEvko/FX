import FX1Poly.Tier0.InternalSconing
import FX1Poly.Tier0.FxThinScopeRMC

/-! # FX1Poly/Tier0/FxThinScopeGlobalSections
    — a zero-axiom `GlobalSections` over the thin scope CwR, via the Yoneda representable presheaf

`FxThinScopeRMC.lean` built the first concrete zero-axiom `RepresentableMapCategory` for FX (the thin
scope-inclusion CwR).  The next stage of the Tier-0 sconing pipeline (`InternalSconing.lean`) needs a
`GlobalSections` over a concrete base category — a contravariant functor `sections : Object -> Type`
(the "terms-in-context" presheaf, `Gamma(A) = closed terms of A`) plus a distinguished object and the
two functor laws.  This file inhabits that interface over the thin scope category, establishing that
the `GlobalSections` / `SconingObject` interfaces are inhabitable at zero axioms — the
global-sections analogue of the RMC-inhabitability result.

## The representable presheaf as the sections functor

The natural funext-free presheaf on the thin scope category is the YONEDA REPRESENTABLE at a chosen
object `topScope`: `sections scope = Hom(scope, topScope) = PLift (scope <= topScope)`.  Its values are
`Prop`-proofs, so — exactly as for the thin category itself — proof irrelevance (definitional in Lean
4's kernel, NOT an axiom) makes both functor laws hold by `rfl`.  The contravariant action is
precomposition: a morphism `a -> b` (a proof `a <= b`) sends `Hom(b, topScope) -> Hom(a, topScope)` by
`le_trans`.  This is a genuine, canonical presheaf — the Yoneda embedding's value at `topScope` — not a
constant/placeholder functor.

## Honest scope boundary

This instantiates the `GlobalSections` interface with the REPRESENTABLE presheaf, demonstrating
inhabitability; it is NOT the intended "closed terms" global-sections of a full type-theoretic CwR
(which needs the term/substitution structure of `fxBaseRMC` proper, awaiting the data-morphism base —
see `FxThinScopeRMC.lean`).  The `terminalObject` field is supplied as `topScope` (the representing
object); the thin scope order `(Nat, <=)` has an INITIAL object (scope 0), not a terminal one, and the
`GlobalSections` structure imposes no universal-property obligation on that field, so this is a
structurally-valid but honestly-degenerate inhabitant.

## What lands here (all zero-axiom)

  * `thinScopeSections` — the representable presheaf `Hom(-, topScope)` as a `Nat -> Nat -> Type`
    family (literal `Nat` parameters so the `<=` never meets the opaque `.Object` projection).
  * `thinScopeGlobalSections` — the `GlobalSections` instance: action by `le_trans`, functor laws by
    proof irrelevance.
  * `thinScopeTautologicalSconing` — the tautological sconing object `S = Gamma(X)`, realization the
    identity, over this `GlobalSections` (the `SconingObject` interface inhabits concretely).

## Zero-axiom verification

The action is `Nat.le_trans` (axiom-free); the functor-law fields are `rfl` (proof irrelevance on the
`PLift`-of-`Prop` sections); the sconing object is the generic `SconingObject.tautological`.  No
`funext` (the sections are `Prop`-valued, so presheaf-naturality needs none).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

/-- The representable presheaf sections at `topScope`: `Hom(scope, topScope) = PLift (scope <=
topScope)`.  Defined with literal `Nat` parameters so the `<=` never sees the opaque `.Object`
projection (which would force an unresolvable `LE thinScopeCategory.Object` instance synthesis). -/
def thinScopeSections (topScope scope : Nat) : Type := PLift (scope ≤ topScope)

/-- **`GlobalSections` over the thin scope CwR, as the Yoneda representable presheaf.**  Sections are
`Hom(-, topScope)`; the contravariant action precomposes a morphism `a -> b` (proof `a <= b`) onto a
section `b -> topScope` by `Nat.le_trans`, landing in `a -> topScope`.  Both functor laws
(`mapsIdentity`, `mapsComposition`) hold by `rfl`: the section values are `Prop`-proofs, so any two
sections of the same object are equal by proof irrelevance.  A genuine canonical presheaf inhabiting
the Tier-0 `GlobalSections` interface (honestly the representable, not the "closed terms" semantics —
see file header). -/
def thinScopeGlobalSections (topScope : Nat) :
    GlobalSections.{0, 0, 0} thinScopeCategory where
  terminalObject := topScope
  sections := thinScopeSections topScope
  sectionMap := fun inclusion sectionAtTarget =>
    PLift.up (Nat.le_trans inclusion.down sectionAtTarget.down)
  mapsIdentity := fun _ _ => rfl
  mapsComposition := fun _ _ _ => rfl

/-- **The tautological sconing object over the thin scope `GlobalSections`.**  `S = Gamma(X)` with the
identity realization (`SconingObject.tautological`) — the concrete witness that the `SconingObject`
interface inhabits over a concrete base category plus its representable `GlobalSections`, the next rung
of the Tier-0 sconing pipeline above the thin RMC. -/
def thinScopeTautologicalSconing (topScope : Nat) (baseScope : Nat) :
    SconingObject thinScopeCategory (thinScopeGlobalSections topScope) :=
  SconingObject.tautological (thinScopeGlobalSections topScope) baseScope

end FX1Poly.Tier0

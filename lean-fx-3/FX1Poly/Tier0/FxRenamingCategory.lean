import FX1Poly.Tier0.RepresentableMapCategory
import FX1Poly.Foundation.RawSubst.RenameDefs

/-! # FX1Poly/Tier0/FxRenamingCategory
    — the first concrete `RawCategory` instance for FX: the renaming (thinning) category

The Tier-0 categorical substrate (`RepresentableMapCategory.lean`, `InternalSconing.lean`, `CwRExtension.lean`)
ships the Uemura CwR interfaces — `RawCategory`, `MorphismClass`, `PullbackSquare`, `RepresentableMapCategory`,
`GlobalSections`, `SconingObject` — but, as their construction-level ledgers record
(`fxSconingConstructionLevel = .extractionRecordInterfaces`, `fxCwRExtensionConstructionLevel =
.extensionComposition`), with NO concrete FX instance: every structure is an obligation shape awaiting an
inhabitant.  The orientation step toward `fxBaseRMC` is to identify what concrete
categorical objects FX already supports and build the first one.

This file builds it: `fxRenamingCategory`, the first concrete `RawCategory` for FX.  Objects are scopes
(`Nat`); morphisms `source ⟶ target` are positional renamings (`RawRenaming source target = Fin source →
Fin target`, the variable-reindexing maps the PolyCell `Fold` engine consumes).  Identity is the identity
renaming; composition is renaming composition.  All three category laws hold definitionally — `composeAssoc`
because function composition is associative, `identityLeft`/`identityRight` by definitional eta — so this is a
genuine, complete, zero-axiom category, not a stub.

## Honest scope boundary

This is the RENAMING (thinning) category — the variable-reindexing base over which NbE / possible-worlds
presheaf models are taken.  It is a legitimate candidate `underlying` for an FX CwR, and the first concrete
inhabitant of the Tier-0 `RawCategory` interface.  It is NOT yet the full `RepresentableMapCategory`
(`fxBaseRMC`): that additionally requires (a) the category of contexts and TERM SUBSTITUTIONS (renamings
are the coarser variable-only fragment), and (b) a distinguished class of representable maps satisfying the
three CwR axioms (closed under pullback with universal property, isomorphisms representable, closed under
composition).  The pullback axiom in particular needs a genuine pullback construction, deferred.  So this lands
the `underlying`-category first piece of fxBaseRMC, honestly NOT the whole RMC.

## What lands here (all zero-axiom)

  * `fxRenamingCategory` — the FX renaming category as a `RawCategory`.
  * `fxRenamingCategory_identity_eq` / `fxRenamingCategory_compose_eq` — the categorical identity / composition
    ARE the renaming identity / composition (the defeq sanity samples connecting the category to the substrate).

## Zero-axiom verification

A `RawCategory` record literal whose three law fields are `rfl` (function-composition associativity + definitional
eta), plus two `rfl` projection lemmas.  No `funext` (function equality of renamings would pull `Quot.sound`),
no induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Foundation

/-- **The FX renaming category.**  Objects are scopes (`Nat`); morphisms are positional renamings
(`RawRenaming source target = Fin source → Fin target`).  Identity is the identity renaming, composition is
renaming composition; the three category laws hold definitionally (associativity of function composition,
definitional eta for the identity laws).  The first concrete `RawCategory` instance for FX — the renaming
(thinning) base, the `underlying`-category first piece of `fxBaseRMC`. -/
def fxRenamingCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := RawRenaming
  identity := fun _scope => RawRenaming.identity
  compose := fun firstRenaming secondRenaming => RawRenaming.compose firstRenaming secondRenaming
  composeAssoc := fun _firstRenaming _secondRenaming _thirdRenaming => rfl
  identityLeft := fun _renaming => rfl
  identityRight := fun _renaming => rfl

/-- The categorical identity of `fxRenamingCategory` IS the identity renaming. -/
theorem fxRenamingCategory_identity_eq {scope : Nat} :
    fxRenamingCategory.identity scope = RawRenaming.identity (scope := scope) := rfl

/-- The categorical composition of `fxRenamingCategory` IS renaming composition. -/
theorem fxRenamingCategory_compose_eq {scopeA scopeB scopeC : Nat}
    (firstRenaming : RawRenaming scopeA scopeB) (secondRenaming : RawRenaming scopeB scopeC) :
    fxRenamingCategory.compose firstRenaming secondRenaming =
      RawRenaming.compose firstRenaming secondRenaming := rfl

end FX1Poly.Tier0

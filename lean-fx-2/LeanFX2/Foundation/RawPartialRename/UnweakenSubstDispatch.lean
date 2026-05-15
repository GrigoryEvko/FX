import LeanFX2.Foundation.RawPartialRename.UnweakenSubstCommute

/-! # Foundation/RawPartialRename/UnweakenSubstDispatch — subst-compat
dispatch corollaries for the propositional-premise architecture.

D2.5.5-Blocker-C deliverable (#1947): turns the `unweaken?_subst_lift_commute`
foundation from #1945 into the dispatch corollaries that compat-cascade
arms of a propositional-premise β rule consume.

The propositional-premise architecture for `transpPi` / `transpSigma`
β rules (#1556 / #1557) takes a Step ctor of shape:

  Step.transpPiBeta
    (codomainUnweakenSuccess : unweaken? codomainCode = some innerCode)
    : Step (transp (pathLam (piTyCode domainCode codomainCode)) source) ...

For the subst-compat arm of such a rule to close, the substituted
hypothesis must still discharge: after `body.subst sigma.lift`, the
`unweaken?` dispatch returns the substituted `inner`.  That is
encoded as the dispatch corollaries below.

These are direct consequences of `unweaken?_subst_lift_commute`;
named explicitly so future cascade arms reference a single lemma
rather than re-deriving the corollary by hand.

## Why this lives in Foundation, not Confluence

The corollaries are pure facts about `unweaken?` and `subst`, with
no dependence on the cd cascade or Step rules.  Foundation is the
correct layer.  Future cascades (D2.5.5/6/7) import this and the
parent commute lemma directly. -/

namespace LeanFX2

/-! ## Dispatch corollaries. -/

/-- If `unweaken? body = some inner`, then after lifting subst under
the binder the same dispatch fires with the substituted inner.
Forward corollary of `unweaken?_subst_lift_commute` for the
positive (β-fires) branch of a propositional-premise rule. -/
theorem RawTerm.unweaken?_subst_lift_dispatch_some
    {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 1))
    (inner : RawTerm sourceScope)
    (sigma : RawTermSubst sourceScope targetScope)
    (dispatchOriginal : RawTerm.unweaken? body = some inner) :
    RawTerm.unweaken? (body.subst sigma.lift) = some (inner.subst sigma) := by
  rw [RawTerm.unweaken?_subst_lift_commute body sigma, dispatchOriginal]
  rfl

/-- If `unweaken? body = none`, then after lifting subst under the
binder the dispatch still returns `none`.  Forward corollary of
`unweaken?_subst_lift_commute` for the negative (β-doesn't-fire)
branch of a propositional-premise rule.  Combined with the
`some` corollary, this gives total coverage of the dispatch's
behaviour under substitution. -/
theorem RawTerm.unweaken?_subst_lift_dispatch_none
    {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 1))
    (sigma : RawTermSubst sourceScope targetScope)
    (dispatchOriginal : RawTerm.unweaken? body = none) :
    RawTerm.unweaken? (body.subst sigma.lift) = none := by
  rw [RawTerm.unweaken?_subst_lift_commute body sigma, dispatchOriginal]
  rfl

end LeanFX2

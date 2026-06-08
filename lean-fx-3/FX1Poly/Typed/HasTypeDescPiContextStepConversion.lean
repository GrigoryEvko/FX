import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.IsTypeDesc

/-! # FX1Poly/Typed/HasTypeDescPiContextStepConversion
    — DIRECTED context conversion under the ENRICHED condition, EXACT classifier (the SR-U route, toward #842/#845/#558)

The grown context-conversion `piElim` arm (GrownCtxConv-5, `#842`) and grown master subject reduction (SRD-2 `#845`
/ SN-055 `#558`) were believed to require the intrinsic logical relation.  They do NOT — that verdict was about the
ARBITRARY-`Conv` context conversion.  Master SR / `TypeCodeValidityRespectsReduction` (`#1094`) needs only the DIRECTED
case: re-type a codomain across a SINGLE stepped domain binder `D ⤳ D'`, with the PREFIX UNCHANGED.

## The enriched condition (the directed-vs-arbitrary distinction, abstracted)

`ConvContextWithOldValid Γ Γ' := ∀ i, Conv (Γ.lookup i) (Γ'.lookup i) ∧ IsTypeDescPi Γ' (Γ.lookup i)` — the old entries
are `Conv` to the new AND ALSO VALID in the new context.  In the var case of context conversion, re-typing `var k` at
its OLD type needs that old type valid in the NEW context.  For ARBITRARY `Conv` the whole prefix changed, so that is the
residual (circular → LR).  For a DIRECTED single step the prefix is IDENTICAL, so the old entry is valid by plain
WEAKENING — FREE.  The enriched condition carries exactly that extra validity, so the var arm conv's back to the EXACT
old classifier (not up-to-`Conv`), and downstream the `piElim` arm reforms EXACTLY with no residual.  The shipped
`HasTypeDesc.convContext` is up-to-`Conv` precisely because it lacked this extra validity (its docstring names "type the
OLD entry under the NEW context — the circularity that sinks the exact-classifier var arm"); the enriched condition
supplies it.

## This file's first brick (SR-U1)

`HasTypeDesc.convContextExactToGrown` — a FORMATION subject re-typed EXACTLY into the GROWN engine under the enriched
condition.  The var conv-back happens at the grown level (`HasTypeDescPi.conv`, since a variable's type may be a grown
code), using the enriched validity; every other formation arm is universe-classified (free).  Formation derivations
cross binders ONLY inside `genFormation`'s telescope (which the shipped exact `DescTelescope.convTelescope` handles with
the plain `Conv` projection), so the enriched validity is used ONLY at the var arm — no cons-lift needed here.  This is
the `ofFormation` arm of the grown context conversion (SR-U2) and the leaf where the directed-step var conv-back lives.

## Zero-axiom verification

Recursion on the formation derivation: var = `HasTypeDescPi.conv` + the enriched validity (the validated linchpin);
universe = `ofFormation ∘ universeFormation`; conv = recurse + grown `conv`; genFormation = `ofFormation ∘ genFormation`
with the shipped `DescTelescope.convTelescope` on the `.1` projection.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The enriched context-conversion condition.**  Old entries are `Conv` to the new entries AND ALSO valid in the new
context.  Free for a directed single step (unchanged prefix ⟹ old entry valid by weakening), but FAILS for arbitrary
`Conv` (old entry valid in the converted prefix = the residual).  This extra validity is what lets the var arm conv back
to the EXACT old classifier (not up-to-`Conv`), so the grown `piElim` arm reforms exactly with no residual. -/
def ConvContextWithOldValid {profile : PolyProfile} {scope : Nat}
    (sourceContext targetContext : TypingContext profile scope) : Prop :=
  ∀ index : Fin scope,
    Conv (sourceContext.lookup index) (targetContext.lookup index) ∧
      IsTypeDescPi profile targetContext (sourceContext.lookup index)

/-- **A formation subject re-typed EXACTLY into the grown engine under the enriched condition.**  The var arm conv's back
to the EXACT old classifier `sourceContext.lookup index` (the validated linchpin: `HasTypeDescPi.conv` with the enriched
condition's old-entry validity supplying the reclassifier typing); universe/genFormation are universe-classified (free,
the latter through the shipped exact `DescTelescope.convTelescope` on the plain-`Conv` projection); conv recurses.  This
is the `ofFormation` leaf of the grown directed context conversion (SR-U2) — where the directed-step var conv-back, the
move impossible for arbitrary `Conv`, lives. -/
theorem HasTypeDesc.convContextExactToGrown {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      ConvContextWithOldValid sourceContext targetContext →
      HasTypeDescPi profile targetContext subject classifier :=
  match derivation with
  | .var _context index => fun targetContext enriched => by
      obtain ⟨convEntry, level, flag, oldEntryTyped⟩ := enriched index
      exact HasTypeDescPi.conv level flag
        (HasTypeDescPi.ofFormation (HasTypeDesc.var targetContext index))
        convEntry.sym oldEntryTyped
  | .conv levelExpr flag typed converts reclassifierTyped => fun targetContext enriched =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDesc.convContextExactToGrown typed targetContext enriched)
        converts
        (HasTypeDesc.convContextExactToGrown reclassifierTyped targetContext enriched)
  | .universeFormation _context levelExpr flag => fun targetContext _enriched =>
      HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation targetContext levelExpr flag)
  | .genFormation _context generator payload children levels flag rule isFormation premises =>
      fun targetContext enriched =>
      HasTypeDescPi.ofFormation
        (HasTypeDesc.genFormation targetContext generator payload children levels flag rule isFormation
          (DescTelescope.convTelescope premises targetContext (fun index => (enriched index).1)))

end FX1Poly.Typed

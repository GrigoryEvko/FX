# Reducibility/Kripke — Kripke Tait reducibility port

Reformulates `Reducible` as a Kripke logical relation: every binder-quantifying arm closes over **all future contexts** reachable by `TermRenaming`, not just the source context.  This unblocks `ReducibleSubst.lift`'s successor case (the K12.20.U4 wall on master).

## Design summary

| Concern | Single-world `Reducible` (master) | Kripke `ReducibleK` (this module) |
| --- | --- | --- |
| Arrow closure | `∀ a in ctx, Reducible A a → Reducible B (app f a)` | `∀ ren : TermRenaming ctx ext, ∀ a in ext at (A.rename rho), ReducibleK (A.rename rho) a → ReducibleK (B.rename rho) (app (f.rename ren) a)` |
| World-weakening | Fails (no inverse rename for closure args) | Trivial — closure already quantifies over extensions |
| `ReducibleSubst.lift` | Blocked at successor case | Direct via world-weakening |
| Lean 4 encoding | `def`-by-Ty-recursion (forced by strict positivity) | Same — but recursive calls on `ty.rename rho` rather than direct sub-Ty |

## Status

- **Phase 1**: PoC for closed leaves + `Ty.arrow`.  Verifies Lean's structural-recursion checker accepts the `ReducibleK (ty.rename rho)` recursive call.
- **Phase 2**: Port remaining 22 Ty arms (sigmaTy, piTy, id-family, parametric, modal, cubical, refine/record/codata/session/effect, cumulUp).
- **Phase 3**: CR2/CR3 for `ReducibleK`.
- **Phase 4**: `ReducibleK.weaken` headline theorem (the unblocker).
- **Phase 5**: `ReducibleSubstK.lift` derived directly from weaken.
- **Phase 6**: Fundamental theorem cases ported to `ReducibleK`.
- **Phase 7**: Switch `Term.strong_normalization` headline to `ReducibleK`.
- **Phase 8**: Retire single-world `Reducible` infrastructure (the IsIdentityLike bypass).

## Open questions

1. Does Lean 4 v4.29.1 accept `ReducibleK (A.rename rho)` as a structurally-decreasing recursive call?  The argument `A.rename rho` is `Ty.rename A rho` — a function application, NOT a literal sub-term of `Ty.arrow A B`.  Lean's structural recursion checker may reject this.
2. If rejected: fallback is step-indexed Kripke (recurse on `Nat` step count) or Ty-size-indexed (banned: `WellFounded`).  Step-indexed is the practical option.
3. The substituted-codomain wall (K12.6 piTy full closure) is NOT fixed by Kripke alone.  piTy stays with weak SN-output closure even after Kripke port.

## References

- Abel-Öhman-Vezzosi POPL 2018, "Decidability of conversion for type theory in type theory" — Agda logical relation
- Wood/Atkey ICFP 2022, "A linear algebra approach to linear metatheory" — corrected Lam rule (already applied in single-world Reducible)
- Allais-Atkey-Chapman-McBride-McKinna ICFP 2018, "A type and scope safe universe of syntaxes with binding" — well-typed renamings as an action

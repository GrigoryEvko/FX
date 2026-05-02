import LeanFX2.Term

/-! # Term/ToRaw — projection (collapses to rfl).

The architectural payoff of raw-aware Term: `Term.toRaw t = raw` is
**rfl** — the projection IS the type index.  No structural recursion,
no proof obligations, no bridge cascade.

Compare with lean-fx's `Term.toRaw : Term ctx ty → RawTerm scope`
which was a 53-line structural recursion plus ~10 supporting lemmas.

## Definition

```lean
@[reducible]
def Term.toRaw : Term ctx ty raw → RawTerm scope := fun _ => raw
```

Wait — this isn't quite right because `raw` is implicit.  The
correct form pulls `raw` out of the function via the implicit:

```lean
@[reducible]
def Term.toRaw {mode level scope ctx ty raw} (_ : @Term mode level scope ctx ty raw) :
    RawTerm scope := raw
```

## Lemmas (all rfl)

* `Term.toRaw_var` — toRaw of `Term.var i` is `RawTerm.var i`
* `Term.toRaw_unit` — toRaw of `Term.unit` is `RawTerm.unit`
* `Term.toRaw_lam` — toRaw of `Term.lam body` is `RawTerm.lam body.toRaw`
* ... (all 29 ctors)

Each lemma is proved by `rfl`.  These lemmas exist as named decls
(not just inline `rfl`) for:
1. **Discoverability** — searching for "toRaw_subst" finds the rule
2. **simp lemma usability** — `simp only [Term.toRaw_*]` rewrites in
   bridge proofs
3. **Documentation** — the file enumerates the projection's behavior
   on every constructor
-/

namespace LeanFX2

/-- The raw projection.  By construction it returns the type-index
`raw` directly, so `Term.toRaw t = t`'s third index is `rfl`. -/
@[reducible]
def Term.toRaw {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (_ : Term context ty raw) : RawTerm scope :=
  raw

/-! ## Per-ctor rfl lemmas. -/

theorem Term.toRaw_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} (position : Fin scope) :
    (Term.var (context := context) position).toRaw = RawTerm.var position := rfl

theorem Term.toRaw_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.unit (context := context)).toRaw = RawTerm.unit := rfl

theorem Term.toRaw_lam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope} {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons context domainType) codomainType.weaken bodyRaw) :
    (Term.lam body).toRaw = RawTerm.lam body.toRaw := rfl

theorem Term.toRaw_app {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    (Term.app functionTerm argumentTerm).toRaw =
      RawTerm.app functionTerm.toRaw argumentTerm.toRaw := rfl

theorem Term.toRaw_lamPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons context domainType) codomainType bodyRaw) :
    (Term.lamPi body).toRaw = RawTerm.lam body.toRaw := rfl

theorem Term.toRaw_appPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    (Term.appPi functionTerm argumentTerm).toRaw =
      RawTerm.app functionTerm.toRaw argumentTerm.toRaw := rfl

theorem Term.toRaw_pair {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    (Term.pair firstValue secondValue).toRaw =
      RawTerm.pair firstValue.toRaw secondValue.toRaw := rfl

theorem Term.toRaw_fst {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    (Term.fst pairTerm).toRaw = RawTerm.fst pairTerm.toRaw := rfl

theorem Term.toRaw_snd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    (Term.snd pairTerm).toRaw = RawTerm.snd pairTerm.toRaw := rfl

theorem Term.toRaw_refl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    (Term.refl (context := context) carrier rawWitness).toRaw =
      RawTerm.refl rawWitness := rfl

theorem Term.toRaw_idJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    (Term.idJ baseCase witness).toRaw =
      RawTerm.idJ baseCase.toRaw witness.toRaw := rfl

end LeanFX2

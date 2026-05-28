import LeanFX2.Foundation.PolyCell.Typed.TypingContextHelpers
import LeanFX2.Foundation.PolyCell.Core.RawTerm

/-! # Foundation/PolyCell/Typed/HasType
   — M34 Phase Z₁: HasType inductive + var rule

M34 (#283, 2026-05-28).  Ships:

* The `HasType` inductive (the typing judgment itself) — empty
  ctor list at this commit; M33 conv-rule + M34 var rule (THIS
  commit's contribution) populate it incrementally.

* The first HasType ctor: `HasType.var` — variable typing per
  M32 #281 TypingContext.lookup.

Per polycell.md §3.16 Phase Z₁ commitment, the typing judgment
is:

  HasType : ∀ {level scope},
    TypingContext level scope →
    RawTerm scope →
    Ty level scope → Prop

The structure: given a typing context Γ, a raw term t, and a
type T, `HasType Γ t T` asserts that t has type T in context Γ.

## What this M34 ships

* `HasType` inductive (Prop-valued, 1 ctor: `var`).  M33-M44
  ctors add per-form arms incrementally.

* `HasType.var` ctor: typed-variable rule per polycell.md.
  Per M32 #281 TypingContext.lookup, variable position `i :
  Fin scope` has type `ctx.lookup i` in context `ctx`.

  Rule statement:
  ```
  HasType ctx (.mkGen .gen_var i .childNil) (ctx.lookup i)
  ```

  Reads: in context ctx, the raw term `.mkGen .gen_var i nil`
  (which is the de Bruijn variable at position i) has type
  `ctx.lookup i` (the binding's type at position i, weakened
  to the lookup scope).

* Smoke witnesses on the M31 #280 fixture contexts
  (singleUnit / twoBindings).

## What this does NOT ship (M33 + M35-M44 task slots)

* **HasType.conv** (M33 #282): type-up-to-Conv coercion.
* **HasType.universe** (M35 #284): universe formation rule.
* **HasType.piTy / lam / app** (M36 #285): function types.
* **HasType.sigmaTy / pair / fst / snd** (M37 #286): pair types.
* **HasType.unit / boolTrue / boolFalse / boolElim** (M38 #287).
* **HasType.natZero / natSucc / natElim / natRec** (M39 #288).
* **HasType.listNil / listCons / listElim** (M40 #289 List).
* **HasType.optionNone / optionSome / optionMatch** (M40 #289 Option).
* **HasType.eitherInl / eitherInr / eitherMatch** (M40 #289 Either).
* **HasType.refl / idJ / idStrictRec** (M41 #290).
* **HasType.cumulUp** (M43 #292): universe cumulativity.
* **HasType.modIntro / modElim / subsume** (M44 #293).

Each subsequent task slot adds CTORS to this inductive.  M34
seeds the inductive with `var`; future tasks extend.

## Why ship the inductive with just `var` at M34

Two design considerations:

1. **Empty Prop inductive is vacuous**: `inductive HasType :
   ... → Prop` with NO ctors is satisfiable only as the empty
   relation.  No theorems about typing would type-check.

2. **var is the simplest non-trivial ctor**: it uses only M31
   TypingContext + M32 lookup, no other Ty rules.  Other ctors
   (universe, Π, Σ, ...) need their own Ty-side machinery that
   ships at their task slots.

So M34 = "HasType inductive + first non-vacuous ctor" gives a
working typing judgment Lean can elaborate against, even before
the full M33-M44 cascade lands.

## Forward-compat: extending HasType

When M33 conv-rule ships, it adds:
```
  | conv {ctx : TypingContext level scope}
         {term : RawTerm scope}
         {sourceType targetType : Ty level scope} :
      HasType ctx term sourceType →
      Conv sourceType targetType →  -- structural Conv between Ty's
      HasType ctx term targetType
```

When M35 universe-formation ships:
```
  | universe {ctx : TypingContext level scope}
             (u : UniverseLevel) (hLe : u.toNat + 1 ≤ level) :
      HasType ctx ... (Ty.universe u hLe)
```

Etc.

## Zero-axiom verification

`HasType` Prop-valued inductive with 1 ctor.  `var` ctor's
witness theorem closes by direct construction.  Smokes close
by `rfl` via fixture pre-evaluations.  No `axiom`, no `sorry`,
no Classical.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Typed

/-- The typing judgment.

`HasType ctx term type` asserts that `term : RawTerm scope`
has `type : Ty level scope` under typing context
`ctx : TypingContext level scope`.

Currently 1 ctor: `var` (typed-variable rule).  M33-M44 task
slots extend with conv / universe / Π / Σ / Unit / bool / Nat /
List / Option / Either / Id / cumul / modal rules. -/
inductive HasType : ∀ {level scope : Nat},
    TypingContext level scope →
    LeanFX2.Foundation.PolyCell.Core.RawTerm scope →
    LeanFX2.Ty level scope →
    Prop
  /-- Typed-variable rule per M32 lookup.  Given a typing
  context `ctx : TypingContext level scope` and a de Bruijn
  position `position : Fin scope`, the raw variable term
  `mkGen .gen_var position .childNil` has the type retrieved
  by `ctx.lookup position`.

  Note: the result type is `ctx.lookup position` — already
  weakened to the lookup scope (per M32's scope-adjustment
  discipline). -/
  | var {level scope : Nat}
        (ctx : TypingContext level scope)
        (position : Fin scope) :
      HasType ctx
        (.mkGen .gen_var position
          (.childNil :
            LeanFX2.Foundation.PolyCell.Core.RawTermChildren []
              scope))
        (ctx.lookup position)

/-! ## Per-fixture var smokes

Demonstrate the var rule firing on the M31-shipped fixture
contexts.  Each smoke instantiates HasType.var at a specific
fixture context + de Bruijn position. -/

/-- Var at position 0 in singleUnit has type
`singleUnit.lookup ⟨0, ...⟩` — which equals `unit.weaken` by
`rfl` via the M32 lookup recursion shape. -/
theorem HasType.var_singleUnit_zero :
    HasType TypingContext.singleUnit
      (.mkGen .gen_var ⟨0, by decide⟩ .childNil)
      (TypingContext.singleUnit.lookup ⟨0, by decide⟩) :=
  HasType.var TypingContext.singleUnit ⟨0, by decide⟩

/-- Var at position 0 in twoBindings has type
`twoBindings.lookup ⟨0, ...⟩` (the innermost bool binding's
type, weakened to twoBindings's scope). -/
theorem HasType.var_twoBindings_zero :
    HasType TypingContext.twoBindings
      (.mkGen .gen_var ⟨0, by decide⟩ .childNil)
      (TypingContext.twoBindings.lookup ⟨0, by decide⟩) :=
  HasType.var TypingContext.twoBindings ⟨0, by decide⟩

/-- Var at position 1 in twoBindings has type
`twoBindings.lookup ⟨1, ...⟩` (the outer unit binding's type,
weakened twice). -/
theorem HasType.var_twoBindings_one :
    HasType TypingContext.twoBindings
      (.mkGen .gen_var ⟨1, by decide⟩ .childNil)
      (TypingContext.twoBindings.lookup ⟨1, by decide⟩) :=
  HasType.var TypingContext.twoBindings ⟨1, by decide⟩

/-! ## Aggregate metric -/

/-- HasType currently has 1 explicit ctor (var).  Advances as
M33-M44 task slots add ctors.  Updates lockstep with the
inductive's actual ctor count. -/
def HasType.ctorCount_M34 : Nat := 1

theorem HasType.ctorCount_M34_correct :
    HasType.ctorCount_M34 = 1 := rfl

end LeanFX2.Foundation.PolyCell.Typed

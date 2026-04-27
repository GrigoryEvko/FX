import FX.KernelMTT.Term
import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.Kernel.Grade
import FX.Kernel.Level
import Tests.Framework

/-!
# FX.KernelMTT.Term tests

Pinning tests for the mode-indexed, well-scoped `Term` inductive
(V1.3 + W2 / R1.4).  Twenty-five tests covering:

  * Construction at each of the four modes (4 tests)
  * `Term.mode` projection on every binder constructor (1 test)
  * `Term.mode` on cross-mode constructors (modIntro, modElim,
    transport) — pins the "target mode wins" rule (3 tests)
  * `structEq` reflexivity on every constructor shape (1 test)
  * `structEq` rejects mode mismatches (2 tests)
  * `structEq` rejects payload mismatches (3 tests)
  * `Inhabited Term` default value pinned (2 tests)
  * HIT primitive replaces Quot — round-trip (3 tests)
  * Cross-mode primitives: ghost ⊣ erase + transport (3 tests)
  * **W2 well-scopedness witnesses** (3 tests) — Fin-indexed
    var construction, lam body in extended context, modElim
    body in extended context.

The W2 tests are positive witnesses; ill-scoped terms cannot be
constructed (Lean type error at construction time, not a
runtime/checker rejection), so negative cases are ENFORCED by
the type system rather than tested at runtime.
-/

namespace Tests.KernelMTT.TermTests

open Tests FX.KernelMTT FX.Kernel

/-! ## Builders for compact test code

   Closed builders are polymorphic in the context size `n` —
   they return `Term n` for any `n`, since they don't reference
   any free variable.  This lets the same builder feed into
   tests at different scopes (e.g. as a domain at `Term n` or as
   a body at `Term (n+1)`).
-/

def boolType {n : Nat} (m : Mode) : Term n := .ind m "Bool" .nil
def natType  {n : Nat} (m : Mode) : Term n := .ind m "Nat" .nil
def trueLit  {n : Nat} (m : Mode) : Term n := .ctor m "Bool" 1 .nil .nil
def natZero  {n : Nat} (m : Mode) : Term n := .ctor m "Nat" 0 .nil .nil

/-- A simple lam `\x : Nat. x` at the given mode.  Closed (n=0).
    The body lives at `Term 1` (one binding in scope), and `var
    0` resolves to the just-bound parameter via `Fin 1`. -/
def identityLamAt (m : Mode) : Term 0 :=
  .lam m Grade.ghost (natType m) (.var m 0)

/-- A simple Pi `Π (_ : Nat) → Nat` at the given mode (Tot
    return effect).  Closed (n=0). -/
def natToNatPi (m : Mode) : Term 0 :=
  .pi m Grade.ghost (natType m) (natType m) Effect.tot

def run : IO Unit := Tests.suite "Tests.KernelMTT.TermTests" do

  -----------------------------------------------------------
  -- Construction at each of the four modes
  -----------------------------------------------------------

  -- 1. Ghost mode — proof-only layer.
  let ghostId := identityLamAt Mode.ghost
  check "ghost mode lam projects ghost"
    Mode.ghost
    ghostId.mode

  -- 2. Software mode — runtime layer (default for FX code).
  let softwareId := identityLamAt Mode.software
  check "software mode lam projects software"
    Mode.software
    softwareId.mode

  -- 3. Hardware mode — synthesizable RTL layer.
  let hardwareId := identityLamAt Mode.hardware
  check "hardware mode lam projects hardware"
    Mode.hardware
    hardwareId.mode

  -- 4. Wire mode — contract-boundary layer.
  let wireId := identityLamAt Mode.wire
  check "wire mode lam projects wire"
    Mode.wire
    wireId.mode

  -----------------------------------------------------------
  -- Term.mode projection covers every binder constructor.
  -- One concrete witness per constructor that carries a mode
  -- field, picked at Software for compactness.  Use Term 3 to
  -- accommodate the maximum var index (2) used in the indRec /
  -- idJ entries.
  -----------------------------------------------------------

  -- 5. Every binder reports its mode correctly.  Use Term 3 to
  --    fit `Term.var s 2` (Fin 3) at indRec / idJ entries.
  --
  --    `TermArgs.ofList` converts `List (Term n)` literals to the
  --    mutual-inductive `TermArgs n`; `.nil` is empty.  Lean's
  --    Coe-from-list doesn't resolve the implicit `n` from
  --    constructor context for empty / weakly-typed list
  --    literals, so the explicit form is required at non-trivial
  --    sites.
  let s := Mode.software
  let allBinders : List (Term 3) := [
    Term.var s 0,
    Term.app s (Term.var s 0) (Term.var s 1),
    Term.lam s Grade.ghost (natType s) (Term.var s 0),
    Term.pi s Grade.ghost (natType s) (natType s) Effect.tot,
    Term.sigma s Grade.ghost (natType s) (natType s),
    Term.type s Level.zero,
    Term.forallLevel s (Term.var s 0),
    Term.const s "myFn",
    Term.ind s "Nat" .nil,
    Term.ctor s "Bool" 1 .nil .nil,
    Term.indRec s "Nat" (Term.var s 0)
      (TermArgs.ofList [Term.var s 1]) (Term.var s 2),
    Term.coind s "Stream" (TermArgs.ofList [natType s]),
    Term.coindUnfold s "Stream"
      (TermArgs.ofList [natType s])
      (TermArgs.ofList [natZero s, Term.var s 0]),
    Term.coindDestruct s "Stream" 0 (Term.var s 0),
    Term.id s (natType s) (natZero s) (natZero s),
    Term.refl s (natZero s),
    Term.idJ s (Term.var s 0) (Term.var s 1) (Term.var s 2),
    Term.hit s "rat" .nil,
    Term.hitMk s "rat" 0 .nil
      (TermArgs.ofList [natZero s, Term.var s 0]),
    Term.hitRec s "rat" (Term.var s 0) .nil .nil (Term.var s 1)
  ]
  let allModesSoftware := allBinders.all (fun t => t.mode == Mode.software)
  check "every binder constructor reports its mode"
    true
    allModesSoftware

  -----------------------------------------------------------
  -- Cross-mode constructors: target-mode wins
  -----------------------------------------------------------

  -- 6. modIntro / modElim / transport project the TARGET mode,
  -- because that's the mode the resulting term lives at.
  -- Take a Ghost-mode value, ghost-lift it to Software via
  -- modIntro: result lives at Software.
  let ghostValue : Term 0 := natZero Mode.ghost
  let ghostLifted : Term 0 :=
    Term.modIntro Mode.ghost Mode.software Modality.usage ghostValue
  -- (Note: `Modality.usage` is just a stand-in here — the real
  -- ghost-lift modality would be a cross-mode adjunction
  -- carrier, which lives in Modality post-V2.20.  For V1.3 the
  -- structural shape is what matters.)
  check "modIntro projects target mode"
    Mode.software
    ghostLifted.mode

  -- modElim: source Software, target Ghost.  Result at target.
  -- The body lives in the context extended by the unwrapped
  -- binding (Term 1), and `var 0` references that binding.
  let elimResult : Term 0 :=
    Term.modElim Mode.software Mode.ghost Modality.usage
      (Term.const Mode.software "x")
      (Term.var Mode.ghost 0)
  check "modElim projects target mode"
    Mode.ghost
    elimResult.mode

  -- transport always lives at the wire boundary.
  let transportResult : Term 0 :=
    Term.transport (Term.const Mode.wire "equiv") (Term.const Mode.wire "x")
  check "transport projects wire mode"
    Mode.wire
    transportResult.mode

  -----------------------------------------------------------
  -- structEq reflexivity + variants
  -----------------------------------------------------------

  -- 7. structEq is reflexive on every binder.
  let allReflexive := allBinders.all (fun t => Term.structEq t t)
  check "structEq is reflexive on all binder constructors"
    true
    allReflexive

  -----------------------------------------------------------
  -- 8. structEq rejects mode mismatches
  -----------------------------------------------------------

  let softwareVar0 : Term 1 := Term.var Mode.software 0
  let ghostVar0    : Term 1 := Term.var Mode.ghost 0
  check "structEq rejects mode mismatch (var)"
    false
    (Term.structEq softwareVar0 ghostVar0)

  -- Same shape across more constructors: lam at different modes.
  let softwareIdLam := identityLamAt Mode.software
  let hardwareIdLam := identityLamAt Mode.hardware
  check "structEq rejects mode mismatch (lam)"
    false
    (Term.structEq softwareIdLam hardwareIdLam)

  -----------------------------------------------------------
  -- 9. structEq rejects payload mismatches
  -----------------------------------------------------------

  -- Same constructor + mode, different content.  Use Term 2 to
  -- fit Fin index 1.
  let var0 : Term 2 := Term.var Mode.software 0
  let var1 : Term 2 := Term.var Mode.software 1
  check "structEq rejects de Bruijn index mismatch"
    false
    (Term.structEq var0 var1)

  let constA : Term 0 := Term.const Mode.software "a"
  let constB : Term 0 := Term.const Mode.software "b"
  check "structEq rejects const name mismatch"
    false
    (Term.structEq constA constB)

  -- Different ctor index in the same inductive.
  let boolFalse : Term 0 := Term.ctor Mode.software "Bool" 0 .nil .nil
  let boolTrue  : Term 0 := Term.ctor Mode.software "Bool" 1 .nil .nil
  check "structEq rejects ctor index mismatch"
    false
    (Term.structEq boolFalse boolTrue)

  -----------------------------------------------------------
  -- 10. Inhabited default
  -----------------------------------------------------------

  -- The `Inhabited Term` instance is the simplest closed form,
  -- `Term.type Mode.ghost Level.zero`, polymorphic in the
  -- context size since `.type` carries no Term subterms.
  let defaultTerm : Term 0 := default
  check "Inhabited default is Type@Ghost level 0"
    Mode.ghost
    defaultTerm.mode

  -- Pin the exact shape via structEq against an explicit
  -- constructor — guards against future Inhabited refactors
  -- silently changing the default.
  let expectedDefault : Term 0 := Term.type Mode.ghost Level.zero
  check "Inhabited default structEq matches explicit form"
    true
    (Term.structEq defaultTerm expectedDefault)

  -----------------------------------------------------------
  -- 11. HIT primitive replaces Quot — three constructors
  -- compose into a recursor application
  -----------------------------------------------------------

  -- A `rat` quotient: `hit "rat" []` is the type, `hitMk "rat" 0
  -- [] [n, d]` is the class constructor (one data ctor), and
  -- `hitRec "rat" motive [classMethod] [eqProof] target` runs
  -- the recursor.  This pins the V2.12-V2.14 shape (HIT
  -- subsumes the Quot family).  Use Term 3 to fit max var
  -- index 2 across all positions.
  let m := Mode.software
  let ratType  : Term 3 := Term.hit m "rat" .nil
  let ratValue : Term 3 := Term.hitMk m "rat" 0 .nil
                            (TermArgs.ofList [natZero m, Term.var m 0])
  let ratLift  : Term 3 := Term.hitRec m "rat"
                            (Term.var m 0)         -- motive
                            (TermArgs.ofList [Term.var m 1])  -- one data method
                            (TermArgs.ofList [Term.var m 2])  -- one path proof
                            ratValue                -- target
  -- Pin all three live at Software.
  check "hit type at software"  Mode.software ratType.mode
  check "hitMk at software"     Mode.software ratValue.mode
  check "hitRec at software"    Mode.software ratLift.mode

  -----------------------------------------------------------
  -- 12. Cross-mode adjunction primitives compose
  -----------------------------------------------------------

  -- ghost ⊣ erase: a value lifted through ghost then erased
  -- back round-trips at the AST level (semantic round-trip is
  -- triangle-identity in V2.20-V2.22; here we just pin the
  -- modes line up).
  let original : Term 0 := natZero Mode.ghost
  let lifted   : Term 0 := Term.modIntro Mode.ghost Mode.software
                            Modality.usage original
  let erased   : Term 0 := Term.modElim Mode.software Mode.ghost
                            Modality.usage lifted
                            (Term.var Mode.ghost 0)
  -- After modIntro: at Software; after modElim back: at Ghost.
  check "ghost-lift round-trip mode chain (lift)"
    Mode.software lifted.mode
  check "ghost-lift round-trip mode chain (erase)"
    Mode.ghost erased.mode

  -- Bonus: structEq distinguishes the lifted vs erased terms
  -- — they're structurally different even though one wraps
  -- the other.
  check "lifted ≠ erased structurally"
    false
    (Term.structEq lifted erased)

  -----------------------------------------------------------
  -- 13. W2 well-scopedness witnesses (NEW for W2)
  -----------------------------------------------------------

  -- A var at idx 0 in a context of size 1 typechecks; the
  -- index resolves to `Fin 1`'s only inhabitant via Lean's
  -- numeric-literal OfNat instance.  Constructing a var at idx
  -- ≥ ctx-size is a Lean type error (no `Fin n` inhabitant for
  -- the literal), so the negative case is enforced by the type
  -- system rather than a runtime check.
  let scopedVar : Term 1 := Term.var Mode.software 0
  check "W2: Fin-indexed var (idx 0, ctx 1)"
    Mode.software
    scopedVar.mode

  -- Lam at ctx 0 has body at ctx 1 — the body's `var 0`
  -- references the just-bound parameter.  This is the
  -- canonical well-scoped lambda shape; the body is at a
  -- DIFFERENT Lean type (Term 1 vs Term 0) than the domain,
  -- which W2 makes structural rather than checker-enforced.
  let extendedLam : Term 0 :=
    Term.lam Mode.software Grade.ghost
      (natType Mode.software) (Term.var Mode.software 0)
  check "W2: lam ctx 0 with body var 0 (Fin 1)"
    Mode.software
    extendedLam.mode

  -- modElim at ctx 0 has body at ctx 1 — the body's `var 0`
  -- references the unwrapped modal value.  Same well-scoping
  -- discipline as lam.
  let unwrap : Term 0 :=
    Term.modElim Mode.software Mode.ghost Modality.usage
      (Term.const Mode.software "x")
      (Term.var Mode.ghost 0)
  check "W2: modElim ctx 0 with body var 0 (Fin 1)"
    Mode.ghost
    unwrap.mode

end Tests.KernelMTT.TermTests

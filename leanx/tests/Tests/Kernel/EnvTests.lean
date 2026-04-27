import FX.Kernel.Env
import Tests.Framework

/-!
# GlobalEnv tests — task A11

`FX.Kernel.GlobalEnv` is the ordered list of top-level
declarations that the elaborator consults when an unqualified
name doesn't match a local binder.  Multi-decl programs resolve
later decls through this registry by inlining the referenced
decl's body.

Covers:
  * `empty` / `addDecl` / `lookup?` / `size`
  * `names` listing (newest-first)
  * `lookupType?` / `lookupBody?` projections
  * `unfold?` — opaque-by-default per §10.15; flips to transparent
    via the explicit flag
  * shadow semantics: re-adding a name returns the newer binding
    on `lookup?` without deleting the old
-/

namespace Tests.Kernel.EnvTests

open FX.Kernel
open Tests

def universeZero : Level := .zero
def typeZero : Term := .type universeZero
def typeOne : Term := .type (.succ .zero)

/-- Option Term equality as Bool — used everywhere the test needs
    to compare two `Option Term` values without DecidableEq. -/
def optTermEq : Option Term → Option Term → Bool
  | none, none       => true
  | some a, some b   => a == b
  | _, _             => false

/-! ## empty env -/

example : GlobalEnv.empty.size = 0 := by decide
example : GlobalEnv.empty.names = [] := by decide
example : (GlobalEnv.empty.lookup? "foo").isNone = true := by decide
example : GlobalEnv.empty.contains "foo" = false := by decide

/-! ## addDecl / lookup? -/

example :
  let globalEnv := GlobalEnv.empty.addDecl "id" typeZero typeOne
  globalEnv.size = 1 := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "id" typeZero typeOne
  (globalEnv.lookup? "id").isSome = true := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "id" typeZero typeOne
  optTermEq (globalEnv.lookupType? "id") (some typeZero) = true := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "id" typeZero typeOne
  optTermEq (globalEnv.lookupBody? "id") (some typeOne) = true := by native_decide

-- Unknown name returns none even after adding other names.
example :
  let globalEnv := GlobalEnv.empty.addDecl "id" typeZero typeOne
  (globalEnv.lookup? "missing").isNone = true := by native_decide

/-! ## names are newest-first -/

example :
  let globalEnv := GlobalEnv.empty.addDecl "a" typeZero typeOne
                                |>.addDecl "b" typeZero typeOne
                                |>.addDecl "c" typeZero typeOne
  globalEnv.names = ["c", "b", "a"] := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "a" typeZero typeOne
                                |>.addDecl "b" typeZero typeOne
                                |>.addDecl "c" typeZero typeOne
  globalEnv.size = 3 := by native_decide

/-! ## shadow semantics — newer entry wins lookup; older stays in list -/

example :
  let globalEnv := GlobalEnv.empty.addDecl "x" typeZero typeOne
                                |>.addDecl "x" typeOne typeZero
  optTermEq (globalEnv.lookupType? "x") (some typeOne) = true := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "x" typeZero typeOne
                                |>.addDecl "x" typeOne typeZero
  -- Size counts both, so the audit trail stays intact.
  globalEnv.size = 2 := by native_decide

/-! ## unfold? — opaque by default, transparent on request -/

example :
  let globalEnv := GlobalEnv.empty.addDecl "opq" typeZero typeOne
  optTermEq (globalEnv.unfold? "opq") none = true := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "trn" typeZero typeOne (transparent := true)
  optTermEq (globalEnv.unfold? "trn") (some typeOne) = true := by native_decide

example : optTermEq (GlobalEnv.empty.unfold? "missing") none = true := by decide

/-! ## Q45 — `reveal` local unfold override

Per `fx_design.md` §10.15: `reveal f;` inside a verify block
locally unfolds an opaque function without flipping the
declaration's published opacity.  The mechanism is a
`revealedNames : List String` field on `GlobalEnv`; `unfold?`
checks BOTH the decl's `transparent` flag AND this list.

Tests below pin:
  * opaque decl: `unfold?` returns `none` without reveal,
    `some body` after `withReveal`
  * transparent decl: `unfold?` always returns `some body`
    (reveal is idempotent with transparent)
  * missing decl: `unfold?` stays `none` even with reveal of the
    missing name (no-op — you can't reveal what isn't there)
  * `withReveals` adds multiple names at once
  * `withReveal` is idempotent (revealing twice = once)
  * `clearReveals` restores the env to no-reveals
  * audit: the original decl's `transparent` flag stays `false`
    after reveal — the override lives in `revealedNames`, not in
    the decl
-/

-- Opaque unfolds only after reveal.
example :
  let globalEnv := GlobalEnv.empty.addDecl "opq" typeZero typeOne
  optTermEq (globalEnv.unfold? "opq") none = true := by native_decide

example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "opq" typeZero typeOne).withReveal "opq"
  optTermEq (globalEnv.unfold? "opq") (some typeOne) = true := by native_decide

-- Revealing a name doesn't bleed into siblings.
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "opq_a" typeZero typeOne
       |>.addDecl "opq_b" typeZero typeOne).withReveal "opq_a"
  optTermEq (globalEnv.unfold? "opq_b") none = true := by native_decide

-- Transparent + reveal = still transparent (idempotent).
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "trn" typeZero typeOne
      (transparent := true)).withReveal "trn"
  optTermEq (globalEnv.unfold? "trn") (some typeOne) = true := by native_decide

-- Revealing an unknown name is a no-op — `unfold?` still returns none.
example :
  let globalEnv := GlobalEnv.empty.withReveal "missing"
  optTermEq (globalEnv.unfold? "missing") none = true := by native_decide

-- `withReveals` handles multiple names in one call.
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "a" typeZero typeOne
       |>.addDecl "b" typeZero typeOne
       |>.addDecl "c" typeZero typeOne).withReveals ["a", "c"]
  optTermEq (globalEnv.unfold? "a") (some typeOne) = true := by native_decide

example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "a" typeZero typeOne
       |>.addDecl "b" typeZero typeOne
       |>.addDecl "c" typeZero typeOne).withReveals ["a", "c"]
  optTermEq (globalEnv.unfold? "b") none = true := by native_decide

example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "a" typeZero typeOne
       |>.addDecl "b" typeZero typeOne
       |>.addDecl "c" typeZero typeOne).withReveals ["a", "c"]
  optTermEq (globalEnv.unfold? "c") (some typeOne) = true := by native_decide

-- Idempotence: revealing twice doesn't duplicate and the unfold
-- behavior is unchanged.
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "opq" typeZero typeOne).withReveal "opq"
                                                   |>.withReveal "opq"
  globalEnv.revealedNames = ["opq"] := by native_decide

-- Clear restores full opacity.
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "opq" typeZero typeOne).withReveal "opq"
                                                   |>.clearReveals
  optTermEq (globalEnv.unfold? "opq") none = true := by native_decide

-- Audit: reveal doesn't mutate the decl's transparent flag.
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "opq" typeZero typeOne).withReveal "opq"
  (globalEnv.lookup? "opq").map (·.transparent) = some false := by native_decide

-- `isTransparent?` reflects reveal: a revealed opaque is "transparent-
-- for-lookup" but the persisted decl flag remains false.
example :
  let globalEnv :=
    (GlobalEnv.empty.addDecl "opq" typeZero typeOne).withReveal "opq"
  globalEnv.isTransparent? "opq" = true := by native_decide

example :
  let globalEnv := GlobalEnv.empty.addDecl "opq" typeZero typeOne
  globalEnv.isTransparent? "opq" = false := by native_decide

/-! ## Trust propagation

Trust defaults to `tested` and propagates as `min` across
transitive `Term.const` references.  A registered-but-sorryT
dep floors every caller's effective trust to `sorryT`;
unregistered refs floor to `external`.  Release builds check
`isReleaseReady = true`, i.e. the transitive trust is `verified`.
-/

-- Default trust is `tested` (not `verified` — release needs explicit upgrade).
example :
  let globalEnv := GlobalEnv.empty.addDecl "x" typeZero typeOne
  globalEnv.transitiveTrust "x" = Trust.tested := by native_decide

-- Trust upgrade: an explicitly-verified decl with no references
-- has transitive trust `verified`.
example :
  let globalEnv := GlobalEnv.empty.addDecl "proven" typeZero typeOne
    (trust := Trust.verified)
  globalEnv.transitiveTrust "proven" = Trust.verified := by native_decide

-- Release gate: `verified` trust AND no unresolved refs.
example :
  let globalEnv := GlobalEnv.empty.addDecl "proven" typeZero typeOne
    (trust := Trust.verified)
  globalEnv.isReleaseReady "proven" = true := by native_decide

-- A decl defaulting to `tested` fails the release gate.
example :
  let globalEnv := GlobalEnv.empty.addDecl "untested" typeZero typeOne
  globalEnv.isReleaseReady "untested" = false := by native_decide

-- Unregistered seed → `external` (bottom).
example :
  GlobalEnv.empty.transitiveTrust "missing" = Trust.external := by native_decide

example :
  GlobalEnv.empty.isReleaseReady "missing" = false := by native_decide

-- Caller referencing an `assumed` dep floors to `assumed`.
example :
  let axiomEnv := GlobalEnv.empty.addDecl "axiom_of_choice" typeZero typeOne
    (trust := Trust.assumed)
  let callerEnv := axiomEnv.addDecl "uses_choice" typeZero
    (.const "axiom_of_choice") (trust := Trust.verified)
  callerEnv.transitiveTrust "uses_choice" = Trust.assumed := by native_decide

-- Caller referencing an `external` dep floors to `external`.
example :
  let externalEnv := GlobalEnv.empty.addDecl "ffi_call" typeZero typeOne
    (trust := Trust.external)
  let callerEnv := externalEnv.addDecl "wraps_ffi" typeZero
    (.const "ffi_call") (trust := Trust.verified)
  callerEnv.transitiveTrust "wraps_ffi" = Trust.external := by native_decide

-- A `sorry`-tainted dep floors the closure to `sorryT`.
example :
  let sorryEnv := GlobalEnv.empty.addDecl "unfinished" typeZero typeOne
    (trust := Trust.sorryT)
  let callerEnv := sorryEnv.addDecl "depends_on_sorry" typeZero
    (.const "unfinished") (trust := Trust.verified)
  callerEnv.transitiveTrust "depends_on_sorry" = Trust.sorryT := by native_decide

-- Min propagates through multi-hop chains: verified → verified → tested
-- floors the root to tested.
example :
  let envLeaf := GlobalEnv.empty.addDecl "leaf_tested" typeZero typeOne
    (trust := Trust.tested)
  let envMid := envLeaf.addDecl "mid_verified" typeZero
    (.const "leaf_tested") (trust := Trust.verified)
  let envRoot := envMid.addDecl "root_verified" typeZero
    (.const "mid_verified") (trust := Trust.verified)
  envRoot.transitiveTrust "root_verified" = Trust.tested := by native_decide

-- An unresolved `const` reference floors to `external`.
example :
  let env := GlobalEnv.empty.addDecl "calls_missing" typeZero
    (.const "never_registered") (trust := Trust.verified)
  env.transitiveTrust "calls_missing" = Trust.external := by native_decide

-- Self-reference doesn't trigger infinite loop.
example :
  let env := GlobalEnv.empty.addDecl "self_ref" typeZero
    (.const "self_ref") (trust := Trust.tested)
  env.transitiveTrust "self_ref" = Trust.tested := by native_decide

/-! ## Runtime harness — `Option Term` has no `DecidableEq`, so
    assertions that compare an `Option Term` result use the
    `optTermEq` helper defined above (compares via Term's `BEq`
    from structEq). -/

def run : IO Unit := Tests.suite "Tests.Kernel.EnvTests" do
  -- empty
  check "empty.size" 0 GlobalEnv.empty.size
  check "empty.names" ([] : List String) GlobalEnv.empty.names
  check "empty.lookup? missing" false (GlobalEnv.empty.lookup? "foo").isSome

  -- single add
  let e1 := GlobalEnv.empty.addDecl "id" typeZero typeOne
  check "add id; size" 1 e1.size
  check "add id; names" ["id"] e1.names
  check "add id; lookupType?" true (optTermEq (some typeZero) (e1.lookupType? "id"))
  check "add id; lookupBody?" true (optTermEq (some typeOne) (e1.lookupBody? "id"))
  check "add id; unfold? opaque" true (optTermEq none (e1.unfold? "id"))

  -- three decls, newest first
  let e3 := GlobalEnv.empty.addDecl "a" typeZero typeOne
                                 |>.addDecl "b" typeZero typeOne
                                 |>.addDecl "c" typeZero typeOne
  check "3-decl names" ["c", "b", "a"] e3.names
  check "3-decl size" 3 e3.size
  check "a still present" true (e3.contains "a")
  check "b still present" true (e3.contains "b")
  check "c still present" true (e3.contains "c")

  -- shadowing
  let shadowedEnv := GlobalEnv.empty.addDecl "x" typeZero typeOne
                                |>.addDecl "x" typeOne typeZero
  check "shadow: newer wins type" true (optTermEq (some typeOne) (shadowedEnv.lookupType? "x"))
  check "shadow: newer wins body" true (optTermEq (some typeZero) (shadowedEnv.lookupBody? "x"))
  check "shadow: size keeps both" 2 shadowedEnv.size

  -- transparent vs opaque
  let opaqueEnv := GlobalEnv.empty.addDecl "opq" typeZero typeOne
  let transparentEnv := GlobalEnv.empty.addDecl "trn" typeZero typeOne
    (transparent := true)
  check "opaque: unfold? = none" true
    (optTermEq none (opaqueEnv.unfold? "opq"))
  check "transparent: unfold? = body" true
    (optTermEq (some typeOne) (transparentEnv.unfold? "trn"))

end Tests.Kernel.EnvTests

import FX.Kernel.Inductive
import Tests.Framework

/-!
# Inductive tests — IndSpec, lookup, strict positivity, iota

Covers `FX/Kernel/Inductive.lean` (task A1):

  * `IndSpec` accessors (`paramCount`, `ctorCount`, `ctorAt?`,
    `findCtor?`).
  * The hardcoded prelude registry (`Bool`, `Nat`, `Unit`, `Empty`).
  * The experimental parameterized specs (`Option`, `List`,
    `Pair`, `Result`) exposed under the `Experimental` namespace
    — intentionally NOT registered in `preludeSpecs` because the
    typing layer does not yet substitute spec type-arguments into
    ctor-arg types (gap noted in the kernel file).
  * `StrictPositivity.absent` — walker over every `Term`
    constructor, exercised both where the name is absent AND
    where it occurs, so a broken short-circuit walker is caught.
  * `StrictPositivity.strictlyPositive` / `isSatisfied` — the
    positivity checker admits `Nat.succ(Nat)` self-reference
    (co-domain-only) and rejects left-of-arrow self-reference,
    plus self-reference nested through `sigma`, `indRec`, `ctor`.

## Worthless-test-avoidance strategy

Spec-lookup checks do NOT stop at `.isSome`: each prelude entry
is pinned by `(specByName? X).map (·.name)`, `.map (·.ctorCount)`,
and `.map (·.ctors.map (·.name))` so a broken lookup that
returns `some <anySpec>` fails.  Strict-positivity is tested
against both well-formed specs (must pass) AND a corpus of
hand-built malformed specs (must fail) covering every term-form
the walker recurses into — a check that always returns `true`
is caught.  The `absent` walker has per-Term-ctor coverage with
both a positive (name appears) and negative (name doesn't)
witness so dropping any match arm produces a test failure.
-/

namespace Tests.Kernel.InductiveTests

open FX.Kernel
open FX.Kernel.Inductive
open Tests

/-! ## Registry lookups — name, ctor count, ctor names pinned -/

example : (specByName? "Bool").map (·.name) = some "Bool"   := by decide
example : (specByName? "Nat").map (·.name)  = some "Nat"    := by decide
example : (specByName? "Unit").map (·.name) = some "Unit"   := by decide
example : (specByName? "Empty").map (·.name) = some "Empty" := by decide
example : specByName? "Unknown"               = none         := by decide
example : (specByName? "Nat").map (·.ctorCount)   = some 2 := by decide
example : (specByName? "Bool").map (·.ctorCount)  = some 2 := by decide
example : (specByName? "Unit").map (·.ctorCount)  = some 1 := by decide
example : (specByName? "Empty").map (·.ctorCount) = some 0 := by decide

example : (specByName? "Bool").map (·.ctors.map (·.name))
  = some ["False", "True"]   := by decide
example : (specByName? "Nat").map (·.ctors.map (·.name))
  = some ["Zero", "Succ"]    := by decide
example : (specByName? "Unit").map (·.ctors.map (·.name))
  = some ["tt"]              := by decide
example : (specByName? "Empty").map (·.ctors.map (·.name))
  = some ([] : List String)  := by decide

/-- A broken `specByName?` that returned any non-none spec for
    every query would be caught: "Bool" must not point at `natSpec`. -/
example : (specByName? "Bool").map (·.ctors.map (·.name))
  ≠ some ["Zero", "Succ"] := by decide
example : (specByName? "Nat").map (·.name) ≠ some "Bool" := by decide

/-! ## `knownName` — pinned against names actually in the registry -/

example : knownName "Bool"    = true  := by decide
example : knownName "Nat"     = true  := by decide
example : knownName "Unit"    = true  := by decide
example : knownName "Empty"   = true  := by decide
example : knownName "Bogus"   = false := by decide
example : knownName ""        = false := by decide
-- Q71: `List` moved into the main prelude for surface list-
-- literal elaboration.  Q75: `Option` moved in for surface
-- `Option.None` / `Option.Some(x)` with expected-type threading.
example : knownName "Option"  = true := by decide
example : knownName "List"    = true := by decide
example : knownName "Pair"    = true := by decide
example : knownName "Result"  = false := by decide

/-! ## Prelude registry shape — cardinality + ordered names

Phase-2 prelude now carries 7 core inductives (Bool, Nat, Unit,
Empty, List added Q71, Option added Q75, Pair added Q79) plus
36 primitive-type tokens per §3.1 (D2).  The 7 core names come
first; primitive names follow in `Inductive.primitiveNumericNames`
order. -/

example : preludeSpecs.length = 7 + 36 := by decide

-- Core inductives at head of list (first 7).
example : (preludeSpecs.take 7).map (·.name) =
    ["Bool", "Nat", "Unit", "Empty", "List", "Option", "Pair"] := by
  decide

-- Primitive tokens at tail (next 36).  Full list pinned in
-- `tests/Tests/Kernel/Grade/PrimitiveTests.lean` per name; here
-- we pin the count to catch accidental add/remove drift. -/
example : ((preludeSpecs.drop 7).map (·.name)).length = 36 := by decide

/-! ## Counts, including `paramCount` (none of the prelude has
parameters — a regression dropping `paramCount` to 0 would be
invisible without these). -/

example : boolSpec.ctorCount  = 2 := by decide
example : boolSpec.paramCount = 0 := by decide
example : natSpec.ctorCount   = 2 := by decide
example : natSpec.paramCount  = 0 := by decide
example : unitSpec.ctorCount  = 1 := by decide
example : unitSpec.paramCount = 0 := by decide
example : emptySpec.ctorCount  = 0 := by decide
example : emptySpec.paramCount = 0 := by decide

/-! ## `findCtor?` — index AND ctor name asserted together -/

example : (boolSpec.findCtor? "False").map (·.fst)       = some 0       := by decide
example : (boolSpec.findCtor? "False").map (·.snd.name)  = some "False" := by decide
example : (boolSpec.findCtor? "True").map (·.fst)        = some 1       := by decide
example : (boolSpec.findCtor? "True").map (·.snd.name)   = some "True"  := by decide
example : boolSpec.findCtor? "NotAnOption" = none                       := by decide
example : boolSpec.findCtor? ""            = none                       := by decide
example : boolSpec.findCtor? "false"       = none                       := by decide  -- case-sensitive

example : (natSpec.findCtor? "Zero").map (·.fst)      = some 0      := by decide
example : (natSpec.findCtor? "Zero").map (·.snd.args.length) = some 0 := by decide
example : (natSpec.findCtor? "Succ").map (·.fst)      = some 1      := by decide
example : (natSpec.findCtor? "Succ").map (·.snd.args.length) = some 1 := by decide

example : (unitSpec.findCtor? "tt").map (·.fst)       = some 0 := by decide
example : (unitSpec.findCtor? "tt").map (·.snd.args.length) = some 0 := by decide

/-! ## `ctorAt?` — name + args length pinned, OOB pinned to `none` -/

example : (boolSpec.ctorAt? 0).map (·.name)        = some "False" := by decide
example : (boolSpec.ctorAt? 0).map (·.args.length) = some 0       := by decide
example : (boolSpec.ctorAt? 1).map (·.name)        = some "True"  := by decide
example : (boolSpec.ctorAt? 1).map (·.args.length) = some 0       := by decide
example : boolSpec.ctorAt? 2 = none := by decide
example : boolSpec.ctorAt? 99 = none := by decide

example : (natSpec.ctorAt? 0).map (·.name)         = some "Zero"  := by decide
example : (natSpec.ctorAt? 0).map (·.args.length)  = some 0       := by decide
example : (natSpec.ctorAt? 1).map (·.name)         = some "Succ"  := by decide
example : (natSpec.ctorAt? 1).map (·.args.length)  = some 1       := by decide
example : natSpec.ctorAt? 2 = none := by decide

example : (unitSpec.ctorAt? 0).map (·.name)        = some "tt"    := by decide
example : unitSpec.ctorAt? 1 = none := by decide

example : emptySpec.ctorAt? 0 = none := by decide

/-! ## Strict positivity — positive cases -/

-- Bool: both ctors nullary, strict positivity trivial.
example : StrictPositivity.isSatisfied boolSpec = true := by decide

-- Nat: Succ's arg is `ind "Nat" []` in final-codomain position
-- (the arg is literally that term, no arrow before it).
example : StrictPositivity.isSatisfied natSpec = true := by decide

-- Unit and Empty trivially pass.
example : StrictPositivity.isSatisfied unitSpec  = true := by decide
example : StrictPositivity.isSatisfied emptySpec = true := by decide

-- Every prelude spec must pass.  A regression that drops any
-- entry's strict positivity is caught.
example : preludeSpecs.all StrictPositivity.isSatisfied = true := by decide

/-! ## Strict positivity — negative fixtures

Each of the following hand-built specs contains a self-reference
in a position the conservative checker rejects.  A broken checker
that always returned `true` would fail these.  The coverage here
exercises every recursive branch of `absent`: pi domain, nested
pi under pi, sigma, indRec, ctor typeName, ctor inside typeArgs /
valueArgs of an outer ctor. -/

/-- `type U Bad(U -> U); end type` — self-ref under the left of
    an arrow is contravariant.  Canonical rejection case. -/
def badSpec : IndSpec :=
  { name := "U"
  , params := []
  , ctors := [
      { name := "Bad"
      , args := [.piTot Grade.default (.ind "U" []) (.ind "U" [])]
      }
    ]
  }

example : StrictPositivity.isSatisfied badSpec = false := by decide

/-- `type V BadDeeper((V -> Type<0>) -> V); end type` — self-ref
    buried under two Pi binders.  The left of the outer arrow is
    the pi term `V -> Type<0>`; `absent` walks into it and finds
    the `V`, so the whole thing is rejected. -/
def deeperBadSpec : IndSpec :=
  { name := "V"
  , params := []
  , ctors := [
      { name := "BadDeeper"
      , args := [.piTot Grade.default
          (.piTot Grade.default (.ind "V" []) (.type .zero))
          (.ind "V" [])]
      }
    ]
  }

example : StrictPositivity.isSatisfied deeperBadSpec = false := by decide

/-- `type W Wrap((x : W) × W); end type` — self-ref as sigma
    carrier.  The conservative checker's `strictlyPositive`
    falls through to `absent` for `sigma`, which walks into both
    fields and finds `W`. -/
def sigmaBadSpec : IndSpec :=
  { name := "W"
  , params := []
  , ctors := [
      { name := "Wrap"
      , args := [.sigma Grade.default (.ind "W" []) (.ind "W" [])]
      }
    ]
  }

example : StrictPositivity.isSatisfied sigmaBadSpec = false := by decide

/-- `type X mk(indRec "X" motive [] target); end type` — self-ref
    via `indRec` rather than a direct `ind`.  The `absent` walker's
    indRec arm must reject names matching `specName`. -/
def indRecBadSpec : IndSpec :=
  { name := "X"
  , params := []
  , ctors := [
      { name := "mk"
      , args := [.indRec "X" (.var 0) [] (.var 1)]
      }
    ]
  }

example : StrictPositivity.isSatisfied indRecBadSpec = false := by decide

/-- `type Y mk(ctor "Y" 0 [] []); end type` — self-ref via a
    `ctor` node.  Catches a walker that only looks at `ind`. -/
def ctorBadSpec : IndSpec :=
  { name := "Y"
  , params := []
  , ctors := [
      { name := "mk"
      , args := [.ctor "Y" 0 [] []]
      }
    ]
  }

example : StrictPositivity.isSatisfied ctorBadSpec = false := by decide

/-- `type Z mk(ctor "Other" 0 [Z] []); end type` — self-ref tucked
    inside the *type args* of an unrelated `ctor` node.  The
    walker must descend into `typeArgs`. -/
def ctorTypeArgBadSpec : IndSpec :=
  { name := "Z"
  , params := []
  , ctors := [
      { name := "mk"
      , args := [.ctor "Other" 0 [.ind "Z" []] []]
      }
    ]
  }

example : StrictPositivity.isSatisfied ctorTypeArgBadSpec = false := by decide

/-- `type Q mk(app (ind "Q" []) (var 0)); end type` — self-ref as
    the function in an `app`.  The walker descends left-and-right. -/
def appBadSpec : IndSpec :=
  { name := "Q"
  , params := []
  , ctors := [
      { name := "mk"
      , args := [.app (.ind "Q" []) (.var 0)]
      }
    ]
  }

example : StrictPositivity.isSatisfied appBadSpec = false := by decide

/-- `type P mk((P = P : Type<0>) arg); end type` — self-ref in
    the id-type's lhs / rhs.  Exercises the `id` arm of `absent`. -/
def idBadSpec : IndSpec :=
  { name := "P"
  , params := []
  , ctors := [
      { name := "mk"
      , args := [.id (.type .zero) (.ind "P" []) (.ind "P" [])]
      }
    ]
  }

example : StrictPositivity.isSatisfied idBadSpec = false := by decide

/-- Sanity: a wholly unrelated spec with no self-reference of any
    kind passes — isolates strictly-positive's positive path. -/
def cleanSpec : IndSpec :=
  { name := "Clean"
  , params := []
  , ctors := [
      { name := "mk"
      , args := [.piTot Grade.default (.ind "Nat" []) (.ind "Nat" [])]
      }
    ]
  }

example : StrictPositivity.isSatisfied cleanSpec = true := by decide

/-! ## Experimental parameterized specs

Not in `preludeSpecs` — see module docstring for the typing-layer
gap.  These tests pin the *spec declaration shape* so any future
relaxation (`paramCount` miscount, ctor list re-ordered) is a
visible regression.  Also verify `StrictPositivity.isSatisfied`
treats `var i` (parameter references) as positive. -/

open FX.Kernel.Experimental

example : optionSpec.name               = "Option" := by decide
example : optionSpec.paramCount         = 1         := by decide
example : optionSpec.ctorCount          = 2         := by decide
example : optionSpec.ctors.map (·.name) = ["None", "Some"] := by decide
example : (optionSpec.ctorAt? 1).map (·.args.length) = some 1 := by decide
example : StrictPositivity.isSatisfied optionSpec = true := by decide

example : listSpec.name               = "List" := by decide
example : listSpec.paramCount         = 1       := by decide
example : listSpec.ctorCount          = 2       := by decide
example : listSpec.ctors.map (·.name) = ["Nil", "Cons"] := by decide
example : (listSpec.ctorAt? 1).map (·.args.length) = some 2 := by decide
-- The recursive `Cons` occurrence `ind "List" [var 0]` is the
-- canonical nested-self-ref pattern the checker admits at the
-- final-codomain position with the parameter threaded through.
example : StrictPositivity.isSatisfied listSpec = true := by decide

example : pairSpec.name               = "Pair" := by decide
example : pairSpec.paramCount         = 2       := by decide
example : pairSpec.ctorCount          = 1       := by decide
example : pairSpec.ctors.map (·.name) = ["MkPair"] := by decide
example : (pairSpec.ctorAt? 0).map (·.args.length) = some 2 := by decide
example : StrictPositivity.isSatisfied pairSpec = true := by decide

example : resultSpec.name               = "Result" := by decide
example : resultSpec.paramCount         = 2         := by decide
example : resultSpec.ctorCount          = 2         := by decide
example : resultSpec.ctors.map (·.name) = ["Ok", "Err"] := by decide
example : (resultSpec.ctorAt? 0).map (·.args.length) = some 1 := by decide
example : (resultSpec.ctorAt? 1).map (·.args.length) = some 1 := by decide
example : StrictPositivity.isSatisfied resultSpec = true := by decide

-- Q71: `List` moved out of Experimental into main prelude.
-- Q75: `Option` moved into main prelude as well.
example : experimentalSpecs.length = 1 := by decide
example : experimentalSpecs.map (·.name) = ["Result"] := by decide
example : experimentalSpecs.all StrictPositivity.isSatisfied = true := by decide

-- `List` (Q71) and `Option` (Q75) are in the prelude now.
-- Phase-2 prelude = 6 core + 36 primitive = 42.  Plus 2
-- experimental = 44.  Update these counts when prelude or
-- experimental registries change.
example : (preludeSpecs ++ experimentalSpecs).length = 7 + 36 + 1 := by decide
example : preludeSpecs.any (·.name == "Option") = true := by decide
example : preludeSpecs.any (·.name == "List")   = true := by decide
example : preludeSpecs.any (·.name == "Pair")   = true := by decide
example : preludeSpecs.any (·.name == "Result") = false := by decide

/-! ## `StrictPositivity.absent` walker — per-Term-constructor

Each constructor of `Term` has (a) at least one *positive*
witness — the spec-name appears somewhere under it, `absent` must
return `false` — and (b) at least one *negative* witness — the
spec-name does not appear, `absent` must return `true`.  A walker
that dropped any arm would flip exactly one of these pairs.

Target name for all walker tests: "Target". -/

namespace AbsentWalker

/-- Helper: a term whose spec-name is "Target" — used everywhere
    below as the needle the walker must detect. -/
abbrev needle : Term := .ind "Target" []

-- `.var` — leaf, no recursion.  Never contains a name.
example : StrictPositivity.absent "Target" (.var 0)  = true := by decide
example : StrictPositivity.absent "Target" (.var 42) = true := by decide

-- `.type` — leaf.  Never contains a name.
example : StrictPositivity.absent "Target" (.type .zero)      = true := by decide
example : StrictPositivity.absent "Target" (.type (.succ .zero)) = true := by decide

-- `.const` — leaf.  The const name is NOT the inductive name the
-- walker checks against, even if it matches the spec name
-- string.  Lock this in so a confused walker doesn't start
-- conflating `.const "Target"` with self-reference.
example : StrictPositivity.absent "Target" (.const "Other")  = true := by decide
example : StrictPositivity.absent "Target" (.const "Target") = true := by decide

-- `.forallLevel` — walker recurses into body.
example : StrictPositivity.absent "Target" (.forallLevel (.var 0))    = true  := by decide
example : StrictPositivity.absent "Target" (.forallLevel needle)      = false := by decide

-- `.coind` post-A2: walker recurses through coind type-args so
-- `ind "Target" …` nested inside a `coind "stream" [...]` is caught.
-- Empty arg list stays true (no Target reference); populated args
-- that contain `ind "Target"` flip to false.
example : StrictPositivity.absent "Target" (.coind "stream" []) = true := by decide
example : StrictPositivity.absent "Target" (.coind "stream" [.ind "Target" []])
    = false := by decide
example : StrictPositivity.absent "Target" (.coind "stream" [.var 0]) = true :=
  by decide

-- `.app` — both function AND argument scanned.
example : StrictPositivity.absent "Target" (.app (.var 0) (.var 1))    = true  := by decide
example : StrictPositivity.absent "Target" (.app needle (.var 0))      = false := by decide
example : StrictPositivity.absent "Target" (.app (.var 0) needle)      = false := by decide

-- `.lam` — both domain AND body scanned.
example : StrictPositivity.absent "Target" (.lam Grade.default (.var 0) (.var 0)) = true  := by decide
example : StrictPositivity.absent "Target" (.lam Grade.default needle (.var 0))   = false := by decide
example : StrictPositivity.absent "Target" (.lam Grade.default (.var 0) needle)   = false := by decide

-- `.pi` — both domain AND body scanned.
example : StrictPositivity.absent "Target" (.piTot Grade.default (.var 0) (.var 0))  = true  := by decide
example : StrictPositivity.absent "Target" (.piTot Grade.default needle (.var 0))    = false := by decide
example : StrictPositivity.absent "Target" (.piTot Grade.default (.var 0) needle)    = false := by decide

-- `.sigma` — both domain AND body scanned.
example : StrictPositivity.absent "Target" (.sigma Grade.default (.var 0) (.var 0)) = true  := by decide
example : StrictPositivity.absent "Target" (.sigma Grade.default needle (.var 0))   = false := by decide
example : StrictPositivity.absent "Target" (.sigma Grade.default (.var 0) needle)   = false := by decide

-- `.id` — eqType, lhs, rhs all scanned.
example : StrictPositivity.absent "Target"
  (.id (.type .zero) (.var 0) (.var 0)) = true := by decide
example : StrictPositivity.absent "Target" (.id needle (.var 0) (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.id (.type .zero) needle (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.id (.type .zero) (.var 0) needle) = false := by decide

-- `.refl` — witness scanned.
example : StrictPositivity.absent "Target" (.refl (.var 0))   = true  := by decide
example : StrictPositivity.absent "Target" (.refl needle)     = false := by decide

-- `.idJ` — motive, base, eq all scanned.
example : StrictPositivity.absent "Target"
  (.idJ (.var 0) (.var 0) (.var 0)) = true := by decide
example : StrictPositivity.absent "Target" (.idJ needle (.var 0) (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.idJ (.var 0) needle (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.idJ (.var 0) (.var 0) needle) = false := by decide

-- `.quot` — carrier AND relation scanned.
example : StrictPositivity.absent "Target"
  (.quot (.var 0) (.var 0)) = true := by decide
example : StrictPositivity.absent "Target" (.quot needle (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.quot (.var 0) needle) = false := by decide

-- `.quotMk` — relation AND witness scanned.
example : StrictPositivity.absent "Target"
  (.quotMk (.var 0) (.var 0)) = true := by decide
example : StrictPositivity.absent "Target" (.quotMk needle (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.quotMk (.var 0) needle) = false := by decide

-- `.quotLift` — lifted, respects, target all scanned.
example : StrictPositivity.absent "Target"
  (.quotLift (.var 0) (.var 0) (.var 0)) = true := by decide
example : StrictPositivity.absent "Target" (.quotLift needle (.var 0) (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.quotLift (.var 0) needle (.var 0)) = false := by decide
example : StrictPositivity.absent "Target" (.quotLift (.var 0) (.var 0) needle) = false := by decide

-- `.ind` — name direct hit AND typeArgs recursion.
example : StrictPositivity.absent "Target" (.ind "Other" [])          = true  := by decide
example : StrictPositivity.absent "Target" (.ind "Other" [.var 0])    = true  := by decide
example : StrictPositivity.absent "Target" needle                     = false := by decide
example : StrictPositivity.absent "Target" (.ind "Other" [needle])    = false := by decide
-- Name match with zero args still a hit.
example : StrictPositivity.absent "Target" (.ind "Target" [])         = false := by decide

-- `.ctor` — typeName AND both arg lists scanned.
example : StrictPositivity.absent "Target"
  (.ctor "Other" 0 [] [])                          = true  := by decide
example : StrictPositivity.absent "Target"
  (.ctor "Target" 0 [] [])                         = false := by decide
example : StrictPositivity.absent "Target"
  (.ctor "Other" 0 [needle] [])                    = false := by decide
example : StrictPositivity.absent "Target"
  (.ctor "Other" 0 [] [needle])                    = false := by decide

-- `.indRec` — typeName, motive, methods, target all scanned.
example : StrictPositivity.absent "Target"
  (.indRec "Other" (.var 0) [] (.var 0))           = true  := by decide
example : StrictPositivity.absent "Target"
  (.indRec "Target" (.var 0) [] (.var 0))          = false := by decide
example : StrictPositivity.absent "Target"
  (.indRec "Other" needle [] (.var 0))             = false := by decide
example : StrictPositivity.absent "Target"
  (.indRec "Other" (.var 0) [needle] (.var 0))     = false := by decide
example : StrictPositivity.absent "Target"
  (.indRec "Other" (.var 0) [] needle)             = false := by decide

end AbsentWalker

/-! ## Runtime harness -/

def run : IO Unit := Tests.suite "Tests.Kernel.InductiveTests" do
  -- Registry pinning
  check "Bool lookup name"         (some "Bool")  ((specByName? "Bool").map (·.name))
  check "Nat lookup name"          (some "Nat")   ((specByName? "Nat").map (·.name))
  check "Unit lookup name"         (some "Unit")  ((specByName? "Unit").map (·.name))
  check "Empty lookup name"        (some "Empty") ((specByName? "Empty").map (·.name))
  check "Unknown lookup is none"   (none : Option String)
    ((specByName? "Unknown").map (·.name))
  check "Bool ctor names in order" (some ["False", "True"])
    ((specByName? "Bool").map (·.ctors.map (·.name)))
  check "Nat ctor names in order"  (some ["Zero", "Succ"])
    ((specByName? "Nat").map (·.ctors.map (·.name)))

  check "Bool registered" true (knownName "Bool")
  check "Nat registered"  true (knownName "Nat")
  check "Unit registered" true (knownName "Unit")
  check "Empty registered" true (knownName "Empty")
  check "Bogus not registered" false (knownName "Bogus")
  check "Option in prelude (Q75)" true (knownName "Option")
  check "List in prelude (Q71)" true (knownName "List")
  check "Pair in prelude (Q79)" true (knownName "Pair")

  -- 7 core inductives (Bool, Nat, Unit, Empty, List, Option,
  -- Pair) + 36 primitive tokens from D2 (i8..i1024, u8..u1024,
  -- isize/usize, int/nat, char/string, decimal/dec32..dec1024,
  -- frac/frac64..frac256, f32/f64).
  check "preludeSpecs size"  (7 + 36) preludeSpecs.length
  check "core prelude names at head"
    ["Bool", "Nat", "Unit", "Empty", "List", "Option", "Pair"]
    ((preludeSpecs.take 7).map (·.name))

  -- ctor / param counts
  check "Bool has 2 ctors"  2 boolSpec.ctorCount
  check "Bool has 0 params" 0 boolSpec.paramCount
  check "Nat has 2 ctors"   2 natSpec.ctorCount
  check "Nat has 0 params"  0 natSpec.paramCount
  check "Unit has 1 ctor"   1 unitSpec.ctorCount
  check "Empty has 0 ctors" 0 emptySpec.ctorCount

  -- Experimental specs — shape pinning
  check "Option paramCount" 1 optionSpec.paramCount
  check "Option ctor names" ["None", "Some"] (optionSpec.ctors.map (·.name))
  check "List paramCount"   1 listSpec.paramCount
  check "List ctor names"   ["Nil", "Cons"] (listSpec.ctors.map (·.name))
  check "Pair paramCount"   2 pairSpec.paramCount
  check "Pair ctor names"   ["MkPair"] (pairSpec.ctors.map (·.name))
  check "Result paramCount" 2 resultSpec.paramCount
  check "Result ctor names" ["Ok", "Err"] (resultSpec.ctors.map (·.name))

  check "experimentalSpecs size"  1 experimentalSpecs.length
  check "experimentalSpecs names" ["Result"]
    (experimentalSpecs.map (·.name))

  -- Positive strict-positivity
  check "Bool strict-positive"    true (StrictPositivity.isSatisfied boolSpec)
  check "Nat strict-positive"     true (StrictPositivity.isSatisfied natSpec)
  check "Unit strict-positive"    true (StrictPositivity.isSatisfied unitSpec)
  check "Empty strict-positive"   true (StrictPositivity.isSatisfied emptySpec)
  check "Option strict-positive"  true (StrictPositivity.isSatisfied optionSpec)
  check "List strict-positive"    true (StrictPositivity.isSatisfied listSpec)
  check "Pair strict-positive"    true (StrictPositivity.isSatisfied pairSpec)
  check "Result strict-positive"  true (StrictPositivity.isSatisfied resultSpec)

  -- Negative strict-positivity corpus
  check "Bad spec rejected"         false (StrictPositivity.isSatisfied badSpec)
  check "Deeper bad spec rejected"  false (StrictPositivity.isSatisfied deeperBadSpec)
  check "Sigma bad spec rejected"   false (StrictPositivity.isSatisfied sigmaBadSpec)
  check "IndRec bad spec rejected"  false (StrictPositivity.isSatisfied indRecBadSpec)
  check "Ctor bad spec rejected"    false (StrictPositivity.isSatisfied ctorBadSpec)
  check "Ctor typeArg bad rejected" false (StrictPositivity.isSatisfied ctorTypeArgBadSpec)
  check "App bad spec rejected"     false (StrictPositivity.isSatisfied appBadSpec)
  check "Id bad spec rejected"      false (StrictPositivity.isSatisfied idBadSpec)
  check "Clean spec accepted"       true  (StrictPositivity.isSatisfied cleanSpec)

  -- `absent` walker spot-checks at runtime (compile-time `by
  -- decide` covers the rest; these are here so a production-
  -- time regression in `partial def absent` shows up if ever the
  -- implementation becomes partial).
  check "absent on var"  true  (StrictPositivity.absent "Target" (.var 0))
  check "absent on needle" false (StrictPositivity.absent "Target" (.ind "Target" []))
  check "absent on app-left-hit" false
    (StrictPositivity.absent "Target" (.app (.ind "Target" []) (.var 0)))
  check "absent on pi-dom-hit"   false
    (StrictPositivity.absent "Target"
      (.piTot Grade.default (.ind "Target" []) (.var 0)))
  check "absent on ctor-name-hit" false
    (StrictPositivity.absent "Target" (.ctor "Target" 0 [] []))
  check "absent on indRec-name-hit" false
    (StrictPositivity.absent "Target" (.indRec "Target" (.var 0) [] (.var 0)))

end Tests.Kernel.InductiveTests

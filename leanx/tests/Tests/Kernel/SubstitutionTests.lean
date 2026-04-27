import FX.Kernel.Substitution

/-!
# Substitution tests

Compile-time tests for `FX.Kernel.Term.shift` and
`FX.Kernel.Term.subst` — both total functions over all 16 Term
forms (var, app, lam, pi, sigma, type, forallLevel, const, ind,
ctor, indRec, coind, id, refl, idJ, quot, quotMk, quotLift).

Test shape: non-trivial closed and open terms, shift/subst
across binders, fixed-point checks (`shift k 0 = id`), coverage
for every constructor including list-carrying ones.

Tests are written so that a broken implementation that returned
its input unchanged (the `id` function) would FAIL — every
assertion either observes a transformation or, when checking a
genuine no-op property, pairs with an adjacent test on a
non-trivial input.
-/

namespace Tests.Kernel.SubstitutionTests

open FX.Kernel
open FX.Kernel.Term

-- `piTot` is defined in `FX.Kernel.Term` (opened above) — builds
-- `Term.pi` with `Effect.tot`.  Pure kernel substitution tests
-- don't exercise effect rows, so this reduces boilerplate after
-- E-1 added the 4th positional `returnEffect` field.

/-! ## Shorthand constructors -/

def universeZero : Level := .zero
def universeOne : Level := .succ .zero
def typeZero : Term := .type universeZero
def typeOne : Term := .type universeOne
def v0 : Term := .var 0
def v1 : Term := .var 1
def v2 : Term := .var 2
def v3 : Term := .var 3
def v4 : Term := .var 4

/-! ## shift — var: below cutoff unchanged, at/above cutoff shifted -/

-- Below cutoff: unchanged — pairs with next test so we can
-- detect a broken `shift` that always shifts regardless of cutoff.
example : shift 3 2 (Term.var 0) = Term.var 0 := rfl
example : shift 3 2 (Term.var 1) = Term.var 1 := rfl
example : shift 3 2 (Term.var 2) = Term.var 2 := rfl

-- At cutoff: shifts by amount — distinct from below-cutoff case.
example : shift 3 2 (Term.var 3) = Term.var 5 := rfl
example : shift 3 2 (Term.var 4) = Term.var 6 := rfl
example : shift 3 2 (Term.var 7) = Term.var 9 := rfl

-- Different non-trivial shift amount to catch wiring errors
-- (e.g., `shift cutoff amount = var (idx + cutoff)` instead of
-- `var (idx + amount)`).
example : shift 1 5 (Term.var 1) = Term.var 6 := rfl
example : shift 1 5 (Term.var 10) = Term.var 15 := rfl

-- shift 0 1 shifts everything by 1
example : shift 0 1 (Term.var 0) = Term.var 1 := rfl
example : shift 0 1 (Term.var 5) = Term.var 6 := rfl

/-! ## shift — type / const: no vars, unchanged by any shift -/

-- We also check on a non-trivial universe level (so a broken
-- shift that stripped the level would be caught by the assertion
-- reconstructing with `universeOne`).
example : shift 0 5 typeZero = typeZero := rfl
example : shift 99 99 typeZero = typeZero := rfl
example : shift 0 5 typeOne = typeOne := rfl
example : shift 3 7 (.type (.succ (.succ .zero))) = .type (.succ (.succ .zero)) := rfl

-- const is a leaf; shift leaves the name intact.  A broken shift
-- that returned `const ""` would fail here.
example : shift 0 5 (.const "foo") = .const "foo" := rfl
example : shift 7 3 (.const "bar") = .const "bar" := rfl
example : shift 0 0 (.const "q") = .const "q" := rfl

-- structEq sanity for const — matching, mismatching, and cross-ctor.
example : ((.const "double" : Term) == (.const "double" : Term)) = true := by
  native_decide
example : ((.const "double" : Term) == (.const "triple" : Term)) = false := by
  native_decide
example : ((.const "x" : Term) == (typeZero : Term)) = false := by
  native_decide
-- Cross-ctor negative: const with same-spelled string vs var
example : ((.const "0" : Term) == (v0 : Term)) = false := by
  native_decide

/-! ## shift — app: both components shifted -/

example : shift 0 1 (Term.app v0 v1) = Term.app v1 v2 := rfl
example : shift 2 3 (Term.app v1 v4) = Term.app v1 (Term.var 7) := rfl
-- Mixed under/over cutoff: detects if only one side is walked.
example : shift 1 10 (Term.app v0 v1) = Term.app v0 (Term.var 11) := rfl

/-! ## shift — lam: body walked under cutoff+1 -/

-- Var 0 inside lam is bound; var 1 references the outer binder
-- and shifts under cutoff+1.  Pair distinguishes the two cases.
example :
  shift 0 1 (Term.lam Grade.default typeZero (Term.var 0))
    = Term.lam Grade.default typeZero (Term.var 0) := rfl

example :
  shift 0 1 (Term.lam Grade.default typeZero (Term.var 1))
    = Term.lam Grade.default typeZero (Term.var 2) := rfl

-- Lam whose domain contains a free var: catches a broken shift
-- that forgets to walk the domain.  The old test used `typeZero`
-- as the domain and so could not detect this bug.
example :
  shift 0 1 (Term.lam Grade.default v0 (Term.var 1))
    = Term.lam Grade.default v1 (Term.var 2) := rfl

-- Deep body: cutoff+1 inside lam, cutoff+2 if nested — but we
-- only have one binder here, so outer var 2 → 7 under amount 5.
example :
  shift 1 5 (Term.lam Grade.default v3 (Term.var 2))
    = Term.lam Grade.default (Term.var 8) (Term.var 7) := rfl

/-! ## shift — pi: same shape as lam, distinct constructor -/

example :
  shift 0 1 (piTot Grade.default typeZero (Term.var 1))
    = piTot Grade.default typeZero (Term.var 2) := rfl

-- Pi with non-trivial domain: catches a shift that walks lam but
-- not pi (copy-paste bug risk since the recursion is
-- constructor-by-constructor).
example :
  shift 0 1 (piTot Grade.default v0 (Term.var 1))
    = piTot Grade.default v1 (Term.var 2) := rfl

-- Grade is preserved: a broken shift returning `Grade.ghost`
-- would fail here because ghost ≠ default.
example :
  shift 0 1 (piTot Grade.ghost typeZero (Term.var 1))
    = piTot Grade.ghost typeZero (Term.var 2) := rfl

/-! ## shift — sigma -/

example :
  shift 0 1 (Term.sigma Grade.default typeZero (Term.var 1))
    = Term.sigma Grade.default typeZero (Term.var 2) := rfl

example :
  shift 0 1 (Term.sigma Grade.default v0 (Term.var 1))
    = Term.sigma Grade.default v1 (Term.var 2) := rfl

/-! ## shift — forallLevel: term-var cutoff passes through unchanged -/

-- The level binder doesn't interact with term-var scope.
example : shift 0 1 (.forallLevel v0) = .forallLevel v1 := rfl
example : shift 2 3 (.forallLevel v4) = .forallLevel (Term.var 7) := rfl
example : shift 0 5 (.forallLevel typeZero) = .forallLevel typeZero := rfl

/-! ## shift — ind / ctor: list-carrying constructors -/

-- Ind type with multiple type args, each containing free vars.
example :
  shift 0 1 (.ind "List" [v0, v1])
    = .ind "List" [v1, v2] := rfl

-- Different ind name preserved: a broken shift returning "" would
-- fail here.
example :
  shift 2 5 (.ind "Map" [v3, v4])
    = .ind "Map" [Term.var 8, Term.var 9] := rfl

-- Empty arg list: leaf case of shiftList.
example :
  shift 0 3 (.ind "Unit" [])
    = .ind "Unit" [] := rfl

-- Ctor: typeArgs AND valueArgs are both walked.  A broken shift
-- that walked only one list would fail here.
example :
  shift 0 1 (.ctor "Pair" 0 [v0, v1] [v2, v3])
    = .ctor "Pair" 0 [v1, v2] [Term.var 3, Term.var 4] := rfl

-- Ctor index preserved: broken shift zeroing the index would fail.
example :
  shift 0 1 (.ctor "Nat" 1 [] [v0])
    = .ctor "Nat" 1 [] [v1] := rfl

-- Ctor name preserved.
example :
  shift 0 1 (.ctor "Succ" 0 [] [v0])
    = .ctor "Succ" 0 [] [v1] := rfl

/-! ## shift — indRec: motive, methods, target all walked -/

-- All three positions contain free vars that should each shift.
-- A broken shift that forgot any of the three would fail.
example :
  shift 0 1 (.indRec "Nat" v0 [v1, v2] v3)
    = .indRec "Nat" v1 [v2, Term.var 3] (Term.var 4) := rfl

-- Empty methods list plus non-trivial motive/target: catches
-- base-case bug in shiftList.
example :
  shift 0 2 (.indRec "Empty" v0 [] v1)
    = .indRec "Empty" v2 [] (Term.var 3) := rfl

/-! ## shift — coind: traverses type-args by name indirection

Post-A2: `Term.coind typeName typeArgs` stores args by
name reference (same pattern as `Term.ind`).  Shift recurses
into the type-arg list; spec lookup happens at typing time, not
at shift. -/

example : shift 0 5 (.coind "stream" []) = (.coind "stream" [] : Term) := rfl
example : shift 3 7 (.coind "stream" []) = (.coind "stream" [] : Term) := rfl
-- Args shift through like any other term-list.
example :
  shift 0 2 (.coind "stream" [v0, v1])
    = (.coind "stream" [v2, Term.var 3] : Term) := rfl

/-! ## shift — id / refl: identity type and its intro -/

-- id: shifts all three fields.
example :
  shift 0 1 (Term.id typeZero v0 v1) = Term.id typeZero v1 v2 := rfl

-- id with free var in type position — catches forgetting to
-- walk the base type.
example :
  shift 0 1 (Term.id v0 v1 v2)
    = Term.id v1 v2 (Term.var 3) := rfl

-- refl: witness walked.
example : shift 0 1 (.refl v0) = .refl v1 := rfl
example : shift 0 1 (.refl typeZero) = .refl typeZero := rfl
example : shift 2 5 (.refl v3) = .refl (Term.var 8) := rfl

/-! ## shift — idJ: three subterms all walked -/

example :
  shift 0 1 (.idJ v0 v1 v2)
    = .idJ v1 v2 (Term.var 3) := rfl

-- Under cutoff 2, only vars ≥ 2 shift.
example :
  shift 2 3 (.idJ v0 v1 v2)
    = .idJ v0 v1 (Term.var 5) := rfl

/-! ## shift — quot / quotMk / quotLift -/

-- quot: shifts both fields, no binder.
example :
  shift 0 1 (Term.quot typeZero v0) = Term.quot typeZero v1 := rfl

example :
  shift 0 1 (Term.quot v0 v1) = Term.quot v1 v2 := rfl

-- quotMk: shifts relation and witness.
example :
  shift 0 1 (.quotMk v0 v1) = .quotMk v1 v2 := rfl

-- quotLift: three subterms.
example :
  shift 0 1 (.quotLift v0 v1 v2)
    = .quotLift v1 v2 (Term.var 3) := rfl

example :
  shift 1 4 (.quotLift v0 v1 v2)
    = .quotLift v0 (Term.var 5) (Term.var 6) := rfl

/-! ## shift_zero: shift by 0 is the identity — paired with
    non-trivial shifts above so a broken `shift = id` fails. -/

example : shift 0 0 typeZero = typeZero := rfl
example : shift 0 0 v0 = v0 := rfl
example : shift 3 0 (Term.app v0 v1) = Term.app v0 v1 := rfl
-- Same cutoff, zero amount on a nested binder: identity holds.
example :
  shift 2 0 (.lam Grade.default v0 (.app v1 v2))
    = .lam Grade.default v0 (.app v1 v2) := rfl

example : ∀ t : Term, shift 0 0 t = t := fun term => Term.shift_zero 0 term

/-! ## subst — var cases (the actual substitution mechanics) -/

-- Match: var 0 replaced by replacement (shift 0 0 replacement).
example : subst 0 typeZero (Term.var 0) = typeZero := rfl

-- Match with non-identity replacement so we see the actual value.
example : subst 0 typeOne (Term.var 0) = typeOne := rfl
example : subst 0 (.const "foo") (Term.var 0) = .const "foo" := rfl

-- Above substitution index: var decrements.
example : subst 0 typeZero (Term.var 1) = Term.var 0 := rfl
example : subst 0 typeZero (Term.var 5) = Term.var 4 := rfl
example : subst 2 typeZero (Term.var 5) = Term.var 4 := rfl
example : subst 2 typeZero (Term.var 3) = Term.var 2 := rfl

-- Below substitution index: var unchanged.
example : subst 1 typeZero (Term.var 0) = Term.var 0 := rfl
example : subst 3 typeZero (Term.var 0) = Term.var 0 := rfl
example : subst 3 typeZero (Term.var 2) = Term.var 2 := rfl
example : subst 5 typeOne (Term.var 4) = Term.var 4 := rfl

-- Replacement itself contains a variable: substituting at index
-- 0 shifts the replacement by 0 (unchanged), at index 2 shifts by 2.
example : subst 0 v0 (Term.var 0) = v0 := rfl
example : subst 2 v0 (Term.var 2) = v2 := rfl  -- replacement shifted by 2
example : subst 3 v1 (Term.var 3) = Term.var 4 := rfl

/-! ## subst — type / const: no vars, unchanged -/

-- Pair these with an adjacent non-trivial subst test so a broken
-- `subst = id` fails on the var case above.
example : subst 0 v0 typeZero = typeZero := rfl
example : subst 7 v4 typeOne = typeOne := rfl
example : subst 0 typeZero (.const "baz") = .const "baz" := rfl
example : subst 3 typeOne (.const "xyz") = .const "xyz" := rfl

/-! ## subst — app: both components walked -/

example :
  subst 0 typeZero (Term.app v0 v1) = Term.app typeZero v0 := rfl

-- Replacement used on both sides when both positions match.
example :
  subst 0 (.const "r") (Term.app v0 v0)
    = Term.app (.const "r") (.const "r") := rfl

-- Above-index vars decrement.
example :
  subst 1 typeZero (Term.app v0 v2)
    = Term.app v0 v1 := rfl

/-! ## subst — lam: body under cutoff+1, domain at cutoff -/

-- The old test used `typeZero` as the domain, hiding any
-- recursion-forgot-the-domain bug.  Use a domain with a free var.
example :
  subst 0 typeOne (Term.lam Grade.default v0 (Term.var 1))
    = Term.lam Grade.default typeOne typeOne := rfl
  -- Domain: var 0 matches subst index 0 → typeOne (shifted by 0).
  -- Body: var 1 matches substitutionIndex+1 = 1 →
  --       shift 0 1 typeOne = typeOne.

-- Body's var 0 is the lam's own binder and stays.
example :
  subst 0 typeOne (Term.lam Grade.default typeZero (Term.var 0))
    = Term.lam Grade.default typeZero (Term.var 0) := rfl

-- Subst into lam whose body references OUTER var (index 1).
-- After subst, outer var 1 matches `substitutionIndex + 1 = 1`,
-- so body gets `shift 0 1 replacement`.
example :
  subst 0 v3 (Term.lam Grade.default typeZero (Term.var 1))
    = Term.lam Grade.default typeZero (Term.var 4) := rfl
  -- Replacement v3 shifted up by 1 under the lam = var 4.

-- Grade preserved through subst.
example :
  subst 0 typeZero (Term.lam Grade.ghost v0 (Term.var 1))
    = Term.lam Grade.ghost typeZero typeZero := rfl

/-! ## subst — pi and sigma: same shape as lam -/

example :
  subst 0 typeOne (piTot Grade.default v0 (Term.var 1))
    = piTot Grade.default typeOne typeOne := rfl

example :
  subst 0 typeOne (Term.sigma Grade.default v0 (Term.var 1))
    = Term.sigma Grade.default typeOne typeOne := rfl

-- Pi/Sigma grade preserved.
example :
  subst 0 typeZero (piTot Grade.ghost v0 v1)
    = piTot Grade.ghost typeZero typeZero := rfl

/-! ## subst — forallLevel: level binder doesn't interact -/

example : subst 0 typeOne (.forallLevel v0) = .forallLevel typeOne := rfl
example : subst 2 v0 (.forallLevel v3) = .forallLevel v2 := rfl

/-! ## subst — ind / ctor / indRec: list-carrying -/

-- ind: each arg walked.
example :
  subst 0 typeOne (.ind "List" [v0, v1])
    = .ind "List" [typeOne, v0] := rfl

-- ctor: typeArgs and valueArgs both walked.
example :
  subst 0 typeOne (.ctor "Pair" 0 [v0, v1] [v2, v3])
    = .ctor "Pair" 0 [typeOne, v0] [v1, v2] := rfl

-- Ctor name and index preserved.
example :
  subst 0 typeOne (.ctor "Succ" 1 [] [v0])
    = .ctor "Succ" 1 [] [typeOne] := rfl

-- indRec: all three subterm positions walked.  Methods list
-- elements all rewritten (a broken substList on one element
-- would fail here).
example :
  subst 0 (.const "r") (.indRec "Nat" v0 [v0, v1] v2)
    = .indRec "Nat" (.const "r") [(.const "r"), v0] v1 := rfl

/-! ## subst — coind: traverses type-args list -/

example : subst 0 typeOne (.coind "stream" []) = (.coind "stream" [] : Term) := rfl
example : subst 7 v4 (.coind "stream" []) = (.coind "stream" [] : Term) := rfl
-- Type-arg list is walked; var 0 in args gets replaced.
example :
  subst 0 typeOne (.coind "stream" [v0, v1])
    = (.coind "stream" [typeOne, v0] : Term) := rfl

/-! ## subst — id / refl / idJ / quot / quotMk / quotLift -/

-- id: three fields all walked.
example :
  subst 0 typeOne (Term.id v0 v1 v2)
    = Term.id typeOne v0 v1 := rfl

-- id with replacement NOT matching any slot — all decrement by 1.
example :
  subst 0 (.const "r") (Term.id v1 v2 v3)
    = Term.id v0 v1 v2 := rfl

-- refl
example : subst 0 typeOne (.refl v0) = .refl typeOne := rfl
example : subst 0 (.const "r") (.refl v1) = .refl v0 := rfl

-- idJ: motive, base, eqProof all walked.
example :
  subst 0 typeOne (.idJ v0 v1 v2)
    = .idJ typeOne v0 v1 := rfl

-- quot: both fields.
example :
  subst 0 typeOne (Term.quot v0 v1) = Term.quot typeOne v0 := rfl

-- quotMk
example :
  subst 0 typeOne (.quotMk v0 v1) = .quotMk typeOne v0 := rfl

-- quotLift: three positions.
example :
  subst 0 typeOne (.quotLift v0 v1 v2)
    = .quotLift typeOne v0 v1 := rfl

/-! ## openWith: canonical beta-step substitution at index 0 -/

example : openWith typeZero (Term.var 0) = typeZero := rfl
example : openWith typeZero (Term.var 1) = Term.var 0 := rfl
example : openWith typeOne (Term.var 0) = typeOne := rfl

-- Real beta-step: `app (lam _ _ body) arg` reduces to
-- `openWith arg body`.  We test the substitution alone here.
example :
  openWith typeOne (Term.app v0 v1) = Term.app typeOne v0 := rfl

-- Opening under a binder-body that references the outer scope.
example :
  openWith typeOne (Term.lam Grade.default typeZero v1)
    = Term.lam Grade.default typeZero typeOne := rfl

/-! ## mentionsVar / countVarAt — binder discipline sanity

These are small smoke tests — not exhaustive, since a dedicated
test file may exist.  Our goal here is to detect a regression
where shift/subst implementations accidentally change the
binder-walking discipline in a way these helpers would also
reflect. -/

-- Lam body's var 0 is bound; outer 0 is not mentioned by var 1
-- nested once (becomes outer 0 after shift).
example : mentionsVar 0 (Term.lam Grade.default typeZero v0) = false := by
  native_decide
example : mentionsVar 0 (Term.lam Grade.default typeZero v1) = true := by
  native_decide

-- Pi walks the same way.
example : mentionsVar 0 (piTot Grade.default v0 v1) = true := by
  native_decide
example : mentionsVar 0 (piTot Grade.default v1 v0) = false := by
  native_decide

-- forallLevel does NOT shift term-var scope.
example : mentionsVar 0 (.forallLevel v0) = true := by native_decide
example : mentionsVar 3 (.forallLevel v3) = true := by native_decide

-- ind/ctor walk into list args.
example : mentionsVar 0 (.ind "List" [v0]) = true := by native_decide
example : mentionsVar 0 (.ind "List" [v1]) = false := by native_decide
example : mentionsVar 2 (.ctor "C" 0 [v0] [v2]) = true := by native_decide

end Tests.Kernel.SubstitutionTests

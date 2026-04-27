import FX.Derived.Session

/-!
# Session → Coind translation tests (task S9)

Compile-time tests pinning the translation of the canonical
`SessionType` examples in `FX.Derived.Session.Binary` to
lists of `CoindSpec`s.

Coverage:

  * Terminal states (`endS`, `stop`) → zero-destructor specs.
  * `send` / `recv` → one-destructor specs with the correct
    destructor name and payload type in the Pi result.
  * `selectS` / `offerS` → one destructor per branch, named
    after the branch label.
  * `loopS` + `continueS` → self-referential spec whose
    continuation points back to the reserved loop name.
  * Malformed input (`continueS` outside `loopS`) → translator
    records a structural error.
  * Canonical examples from `Binary.lean` produce the
    expected spec counts.

All checks use `native_decide` because `translate` is a
`partial def` over `SessionType` and `ofSession` / `ofBranches`
are mutually recursive, which blocks kernel reduction for
`decide`.  Native compilation handles `partial def` fine.
-/

namespace Tests.Derived.SessionTranslateTests

open FX.Derived.Session
open FX.Kernel

/-! ## Terminal states -/

example :
    (translate "Trial" SessionType.endS).specs.length == 1 := by native_decide

example :
    (translate "Trial" SessionType.endS).rootName == "Trial_0" := by native_decide

example :
    (translate "Trial" SessionType.endS).specs.head!.destructors.length == 0 := by
  native_decide

-- `stop` has the same translation shape as `endS`.
example :
    (translate "Trial" SessionType.stop).specs.length == 1 := by native_decide

example :
    (translate "Trial" SessionType.stop).specs.head!.destructors.length == 0 := by
  native_decide

/-! ## Send / recv chains -/

private def natPayload : Term := Term.ind "Nat" []

-- `send(Nat, endS)` produces 2 specs: cont first, then the send head.
example :
    (translate "Chan" (.send natPayload .endS)).specs.length == 2 := by native_decide

/-- The root spec (which matches the send head) has one destructor. -/
example :
    let result := translate "Chan" (.send natPayload .endS)
    (match result.specByName? result.rootName with
     | some spec => spec.destructors.length == 1
     | none      => false) = true
  := by native_decide

-- The root's one destructor is named "send".
example :
    let result := translate "Chan" (.send natPayload .endS)
    (match result.specByName? result.rootName with
     | some spec =>
       match spec.destructors with
       | dest :: _ => dest.name == "send"
       | []        => false
     | none => false) = true
  := by native_decide

-- `recv(Nat, endS)` symmetric: destructor "recv".
example :
    let result := translate "Chan" (.recv natPayload .endS)
    (match result.specByName? result.rootName with
     | some spec =>
       match spec.destructors with
       | dest :: _ => dest.name == "recv"
       | []        => false
     | none => false) = true
  := by native_decide

-- `send(Nat, recv(Nat, endS))` — 3 specs total.
example :
    (translate "Chan"
      (.send natPayload (.recv natPayload .endS))).specs.length == 3 := by
  native_decide

/-! ## Branching -/

private def twoBranchSelect : SessionType :=
  .selectS [("left", .endS), ("right", .endS)]

-- Two-branch select produces 1 root spec + 2 continuation specs = 3.
example :
    (translate "Sel" twoBranchSelect).specs.length == 3 := by native_decide

-- The root's destructors are named "left" and "right" in order.
example :
    let result := translate "Sel" twoBranchSelect
    (match result.specByName? result.rootName with
     | some spec => spec.destructors.map (·.name) == ["left", "right"]
     | none      => false) = true
  := by native_decide

-- offerS has identical structural shape at the type level.
example :
    let result := translate "Off" (.offerS [("a", .endS), ("b", .endS)])
    (match result.specByName? result.rootName with
     | some spec => spec.destructors.map (·.name) == ["a", "b"]
     | none      => false) = true
  := by native_decide

/-! ## Loops + continueS -/

-- `loopS (send T continueS)` produces 1 spec: the loop's spec with a
-- single send destructor that references the loop's own name.
private def simpleLoop : SessionType :=
  .loopS (.send natPayload .continueS)

example :
    (translate "Loop" simpleLoop).specs.length == 1 := by native_decide

example :
    (translate "Loop" simpleLoop).rootName == "Loop_0" := by native_decide

example :
    let result := translate "Loop" simpleLoop
    (match result.specByName? result.rootName with
     | some spec => spec.destructors.length == 1
     | none      => false) = true
  := by native_decide

-- The send destructor's result type references the loop's own name.
example :
    let result := translate "Loop" simpleLoop
    (match result.specByName? result.rootName with
     | some spec =>
       match spec.destructors with
       | dest :: _ =>
         match dest.resultType with
         | Term.pi _ _ (Term.coind contName _) _ => contName == "Loop_0"
         | _ => false
       | []        => false
     | none => false) = true
  := by native_decide

/-! ## Orphan continueS (malformed input) -/

-- `continueS` at the top level records an error.
example :
    (translate "Bad" SessionType.continueS).errors.length == 1 := by native_decide

example :
    (translate "Bad" SessionType.continueS).wasSuccessful == false := by native_decide

-- Well-formed inputs have no errors.
example :
    (translate "Good" SessionType.endS).wasSuccessful == true := by native_decide

example :
    (translate "Good" simpleLoop).wasSuccessful == true := by native_decide

/-! ## Canonical examples from Binary.lean

Cross-validate the translation against the named examples
`SessionType.requestResponseOnce`, `requestResponseLoopClient`,
and `authClient`.  Pinning spec counts catches regressions in
the translator's handling of compound shapes. -/

-- send(Request) then recv(Response) then endS: 3 specs.
example :
    (translate "RR"
      SessionType.requestResponseOnce).specs.length == 3 := by native_decide

-- `requestResponseLoopClient`: loopS(send. recv. continueS).
-- Inside the loop: send is the root (gets loop name), then recv — total 2.
example :
    (translate "RRL"
      SessionType.requestResponseLoopClient).specs.length == 2 := by native_decide

-- `authClient`: send(Creds). offerS(success → recv.endS,
-- failure → recv.endS).  Counts:
--   * 2 endS specs (success, failure terminators)      = 2
--   * 2 recv specs (one per branch)                    = 2
--   * 1 offerS spec                                    = 1
--   * 1 send spec (root)                               = 1
-- total = 6.
example :
    (translate "Auth" SessionType.authClient).specs.length == 6 := by native_decide

/-! ## Ordering invariant

Continuations are emitted BEFORE their referents — a spec's
destructors only reference names that appear earlier in the
`specs` list.  This is the reverse-topological order the
kernel global env needs for safe registration. -/

-- For `send(T, endS)`, the cont (endS) spec is listed first.
example :
    let result := translate "Ord" (.send natPayload .endS)
    result.specs.head!.destructors.length == 0 := by native_decide

/-! ## Kernel soundness pass

Every generated `CoindSpec` passes the kernel's guardedness
check (`Guarded.isSatisfied`).  The guardedness rule (§H.5
Coind-ν) requires self-references to live in final-codomain
position; our translation satisfies this because:

  * send / recv destructors use `Pi _ payload (coind contName
    [])` — the cont is in codomain position, the payload
    doesn't mention the spec name (payloads are external
    kernel terms).
  * select / offer destructors use `coind contName []`
    directly — final-codomain is trivially final.
  * loopS uses its own reserved name as the cont — also in
    codomain position.

Pin this for the canonical examples. -/

example :
    (translate "Trial" SessionType.endS).specs.all
      (fun spec => Guarded.isSatisfied spec) == true := by native_decide

example :
    (translate "Chan" (.send natPayload .endS)).specs.all
      (fun spec => Guarded.isSatisfied spec) == true := by native_decide

example :
    (translate "Loop" simpleLoop).specs.all
      (fun spec => Guarded.isSatisfied spec) == true := by native_decide

example :
    (translate "RR" SessionType.requestResponseOnce).specs.all
      (fun spec => Guarded.isSatisfied spec) == true := by native_decide

example :
    (translate "Auth" SessionType.authClient).specs.all
      (fun spec => Guarded.isSatisfied spec) == true := by native_decide

end Tests.Derived.SessionTranslateTests

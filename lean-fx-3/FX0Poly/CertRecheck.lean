import FX0Poly.StructuralRecheck

/-!
# FX0Poly — recursive certificate re-check driver

`StructuralRecheck` defines the single-node admission rule (`recheckNode`).  This file ships the RECURSIVE
DRIVER that folds it over a whole certificate tree: re-check every child, then apply the per-node rule to
the node's tag and its children's verdicts.

A `Cert` is the flat, self-contained tree the minimal checker re-checks — a generator tag plus the child
certificates — deliberately INDEPENDENT of FX1Poly's in-memory `RawCell`: the checker never sees FX1Poly's
data structures, only this re-serializable record.  The descent is purely structural (mutual recursion with
`recheckChildren`): no fuel, no well-founded recursion, no termination obligation — the Metamath-Zero
discipline of a tiny total checker.

This file ships the driver, its length-preservation invariant, and a recursive-descent non-vacuity corpus.
The full recursive soundness (`recheck` accepts exactly the structurally-valid trees) lives in
`CertRecheckSound`.

## Zero-axiom verification

`Cert.recheck` / `recheckChildren` are total mutual structural recursions; `recheckChildren_length` is a
plain `List` induction; the smokes close by `rfl` (full evaluation).  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX0Poly

/-- A structural certificate tree: a generator tag with its child certificates.  The self-contained record
the minimal checker re-checks, independent of FX1Poly's `RawCell`. -/
inductive Cert where
  | node (tag : Nat) (children : List Cert)

mutual
  /-- The recursive re-check driver: re-check every child, then apply the per-node admission rule
  `recheckNode` with the node's expected arity (from the tag→arity model `arity`).  Mutually structural
  with `recheckChildren`. -/
  def Cert.recheck (arity : Nat → Option Nat) : Cert → CheckVerdict
    | .node tag children => recheckNode (arity tag) (Cert.recheckChildren arity children)
  /-- Re-check a list of child certificates left-to-right, one verdict per child. -/
  def Cert.recheckChildren (arity : Nat → Option Nat) : List Cert → List CheckVerdict
    | [] => []
    | c :: rest => Cert.recheck arity c :: Cert.recheckChildren arity rest
end

/-- **Length preservation of the child driver.**  `recheckChildren` produces exactly one verdict per
child, so the per-node arity check (`recheckNode`, which compares the verdict count to the expected arity)
is comparing the node's TRUE child count.  Plain structural induction on the child list. -/
theorem Cert.recheckChildren_length (arity : Nat → Option Nat) (children : List Cert) :
    (Cert.recheckChildren arity children).length = children.length := by
  induction children with
  | nil => rfl
  | cons c rest ih =>
      show (Cert.recheck arity c :: Cert.recheckChildren arity rest).length = (c :: rest).length
      rw [List.length_cons, List.length_cons, ih]

/-- Non-vacuity: a leaf node whose tag has arity `0` re-checks as accepted. -/
theorem Cert.recheck_smoke_leafAccepted :
    Cert.recheck (fun _tag => some 0) (.node 7 []) = CheckVerdict.accepted := rfl

/-- Non-vacuity: a node whose tag is unknown (`none` arity) is malformed regardless of its children. -/
theorem Cert.recheck_smoke_unknownTag :
    Cert.recheck (fun _tag => none) (.node 7 [.node 0 []]) = CheckVerdict.malformed := rfl

/-- Non-vacuity (recursive descent): a binary node (tag `1`, arity 2) over two well-formed arity-0 leaves
re-checks accepted — the driver descends, accepts the leaves, then admits the parent. -/
theorem Cert.recheck_smoke_recursiveAccepted :
    Cert.recheck (fun tag => if tag == 1 then some 2 else some 0)
        (.node 1 [.node 2 [], .node 3 []]) = CheckVerdict.accepted := rfl

/-- Non-vacuity (rejection propagates): one child is ill-formed (an arity-0 tag given a child), so the
whole tree is malformed — the child's rejection propagates up through the per-node rule. -/
theorem Cert.recheck_smoke_recursiveRejected :
    Cert.recheck (fun tag => if tag == 1 then some 2 else some 0)
        (.node 1 [.node 2 [], .node 3 [.node 0 []]]) = CheckVerdict.malformed := rfl

end FX0Poly

import FX0Poly.CertRecheck

/-!
# FX0Poly — recursive re-check soundness (the driver accepts exactly the structurally-valid trees)

`CertRecheck` defines the recursive driver `Cert.recheck`.  This file proves it **sound and complete**: the
driver accepts a certificate tree EXACTLY when the tree is structurally valid — every node's generator tag
has a known arity matching its child count, recursively.

`Cert.isValidB` is the intrinsic recursive Boolean validity predicate (the spec); the soundness theorem
`Cert.recheck_wasAccepted_eq_isValidB` states the driver's acceptance `Bool` EQUALS `isValidB` at every
tree.  Stated as a `Bool` equality (not a `Prop` `Iff`) to stay `propext`-free — the Metamath-Zero form,
where the trusted checker and its specification are both total `Bool` computations.

The proof is a mutual structural recursion mirroring the driver: the node case composes the per-node Bool
soundness (`recheckNode_some_wasAccepted_eq`), the length invariant (`recheckChildren_length`), and the
child-list lemma; the list case composes `List.all_cons` with the two recursive hypotheses.  No fuel, no
well-founded recursion.

## Zero-axiom verification

All proofs reduce to `recheckNode_some_wasAccepted_eq`, `recheckChildren_length`, `List.all_cons`, a `cases`
on `arity tag`, and `rfl` — no `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Gated per-declaration in `FX1PolyAudit/AuditFX0Poly.lean`.
-/

namespace FX0Poly

mutual
  /-- Intrinsic recursive Boolean validity of a certificate tree (the specification the checker
  re-derives): a node is valid iff its generator tag has a known arity `n`, its child count equals `n`, and
  every child is recursively valid.  Mutually structural with `allValidB`. -/
  def Cert.isValidB (arity : Nat → Option Nat) : Cert → Bool
    | .node tag children =>
      match arity tag with
      | none => false
      | some n => (children.length == n) && Cert.allValidB arity children
  /-- Every certificate in a list is recursively valid. -/
  def Cert.allValidB (arity : Nat → Option Nat) : List Cert → Bool
    | [] => true
    | c :: rest => Cert.isValidB arity c && Cert.allValidB arity rest
end

mutual
  /-- **Soundness and completeness of the recursive driver.**  The driver `Cert.recheck` accepts a
  certificate tree EXACTLY when the tree is structurally valid: its acceptance `Bool` equals the intrinsic
  validity `Cert.isValidB`, at every tree.  Mutually structural with the child-list lemma; the node case
  composes the per-node Bool soundness, the length invariant, and the child-list lemma. -/
  theorem Cert.recheck_wasAccepted_eq_isValidB (arity : Nat → Option Nat) :
      ∀ c : Cert, (Cert.recheck arity c).wasAccepted = Cert.isValidB arity c
    | .node tag children => by
        show (recheckNode (arity tag) (Cert.recheckChildren arity children)).wasAccepted =
          (match arity tag with
           | none => false
           | some n => (children.length == n) && Cert.allValidB arity children)
        cases arity tag with
        | none => rfl
        | some n =>
            rw [recheckNode_some_wasAccepted_eq, Cert.recheckChildren_length,
                Cert.recheckChildren_all_wasAccepted_eq_allValidB arity children]
  /-- The child driver's all-accepted `Bool` equals the list's recursive validity `allValidB`. -/
  theorem Cert.recheckChildren_all_wasAccepted_eq_allValidB (arity : Nat → Option Nat) :
      ∀ children : List Cert,
        (Cert.recheckChildren arity children).all CheckVerdict.wasAccepted = Cert.allValidB arity children
    | [] => rfl
    | c :: rest => by
        show (Cert.recheck arity c :: Cert.recheckChildren arity rest).all CheckVerdict.wasAccepted =
          (Cert.isValidB arity c && Cert.allValidB arity rest)
        rw [List.all_cons, Cert.recheck_wasAccepted_eq_isValidB arity c,
            Cert.recheckChildren_all_wasAccepted_eq_allValidB arity rest]
end

/-- Non-vacuity: the intrinsic validity predicate accepts a genuinely well-formed tree (so the soundness
equation is not the vacuous `false = false`). -/
theorem Cert.isValidB_smoke_valid :
    Cert.isValidB (fun tag => if tag == 1 then some 2 else some 0)
      (.node 1 [.node 2 [], .node 3 []]) = true := rfl

end FX0Poly

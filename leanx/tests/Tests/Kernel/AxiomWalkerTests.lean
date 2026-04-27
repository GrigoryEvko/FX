import FX.Kernel.AxiomWalker

/-!
# Axiom walker tests (F5)

Compile-time checks on `FX.Kernel.Term.collectAxioms`:

  1. Head-level axiom extraction — each Term constructor's
     `ofHeadAxioms` returns the right H-N citation.
  2. Deep walker — `collectAxioms` unions child axioms into the
     root node's head axioms.
  3. Dedup — repeated axioms across the tree appear once.
  4. Sort ordering — `sortAxioms` produces output in canonical
     Appendix-H order.

A failed test here breaks the `fxi show-axioms` CLI's trust-base
report; these examples are the contract between the walker and
the CLI presenter.
-/

namespace Tests.Kernel.AxiomWalker

open FX.Kernel

/-! ## Head-level axiom table

One `example` per Term constructor, pinning the exact `KernelAxiom`
list returned by `ofHeadAxioms`.  Grade fields are filled with
`Grade.ghost` (the minimum-information grade) since the axiom
extraction does not inspect grade contents. -/

example : Term.ofHeadAxioms (.var 0) = [] := rfl
example : Term.ofHeadAxioms (.app (.var 0) (.var 1)) = [.piElim] := rfl
example : Term.ofHeadAxioms (.lam Grade.ghost (.var 0) (.var 0)) = [.piIntro] := rfl
example : Term.ofHeadAxioms (.pi Grade.ghost (.var 0) (.var 0) Effect.tot) = [.piForm] := rfl
example : Term.ofHeadAxioms (.sigma Grade.ghost (.var 0) (.var 0)) = [.sigmaForm] := rfl
example : Term.ofHeadAxioms (.type .zero) = [.uWf, .uHier] := rfl
example : Term.ofHeadAxioms (.forallLevel (.var 0)) = [.uPoly] := rfl
example : Term.ofHeadAxioms (.const "foo") = [] := rfl
example : Term.ofHeadAxioms (.ind "Nat" []) = [.indForm] := rfl
example : Term.ofHeadAxioms (.ctor "Nat" 0 [] []) = [.indIntro] := rfl
example : Term.ofHeadAxioms (.indRec "Nat" (.var 0) [] (.var 1)) = [.indElim] := rfl
example : Term.ofHeadAxioms (.id (.var 0) (.var 1) (.var 2)) = [.idForm] := rfl
example : Term.ofHeadAxioms (.refl (.var 0)) = [.idRefl] := rfl
example : Term.ofHeadAxioms (.idJ (.var 0) (.var 1) (.var 2)) = [.idJ] := rfl
example : Term.ofHeadAxioms (.quot (.var 0) (.var 1)) = [.quotForm] := rfl
example : Term.ofHeadAxioms (.quotMk (.var 0) (.var 1)) = [.quotMk] := rfl
example : Term.ofHeadAxioms (.quotLift (.var 0) (.var 1) (.var 2)) = [.quotLift] := rfl
-- Coind head citation (post-A2: `Term.coind typeName typeArgs`).
example : Term.ofHeadAxioms (.coind "stream" []) = [.coindForm] := rfl
example : Term.ofHeadAxioms (.coind "stream" [.var 0]) = [.coindForm] := rfl

/-! ## Deep walker — composition

A lambda over a sigma-typed domain should report both Pi-intro
(for the lambda) and Sigma-form (for the domain type). -/

example :
    (Term.collectAxioms
      (.lam Grade.ghost
        (.sigma Grade.ghost (.type .zero) (.var 0))
        (.var 0))).contains .piIntro = true := by
  native_decide

example :
    (Term.collectAxioms
      (.lam Grade.ghost
        (.sigma Grade.ghost (.type .zero) (.var 0))
        (.var 0))).contains .sigmaForm = true := by
  native_decide

/-- An identity-eliminator term invokes Id-J directly and Id-form
    through the motive's type.  Deep walker picks up both. -/
example :
    (Term.collectAxioms
      (.idJ
        (.pi Grade.ghost (.type .zero)
          (.id (.var 0) (.var 0) (.var 0)) Effect.tot)
        (.refl (.var 0))
        (.refl (.var 0)))).contains .idJ = true := by
  native_decide

example :
    (Term.collectAxioms
      (.idJ
        (.pi Grade.ghost (.type .zero)
          (.id (.var 0) (.var 0) (.var 0)) Effect.tot)
        (.refl (.var 0))
        (.refl (.var 0)))).contains .idRefl = true := by
  native_decide

example :
    (Term.collectAxioms
      (.idJ
        (.pi Grade.ghost (.type .zero)
          (.id (.var 0) (.var 0) (.var 0)) Effect.tot)
        (.refl (.var 0))
        (.refl (.var 0)))).contains .idForm = true := by
  native_decide

/-! ## Deep walker — Coind args

`collectAxioms` recurses into a coind type's arg list per A2's
name-indirection shape.  An axiom invoked inside a coind type
argument surfaces in the parent's axiom set. -/

-- `coind "stream" [.refl witness]` invokes both Coind-form (from
-- the coind head) and Id-refl (from the refl witness argument).
example :
    (Term.collectAxioms
      (.coind "stream" [.refl (.var 0)])).contains .coindForm = true := by
  native_decide

example :
    (Term.collectAxioms
      (.coind "stream" [.refl (.var 0)])).contains .idRefl = true := by
  native_decide

-- Empty args: coind head axiom alone, no extra child contributions.
example :
    (Term.collectAxioms (.coind "stream" [])) = [.coindForm] := by native_decide

/-! ## Deduplication

Repeated axioms across sibling sub-terms appear once. -/

example :
    ((Term.collectAxioms
      (.app (.lam Grade.ghost (.type .zero) (.var 0))
            (.lam Grade.ghost (.type .zero) (.var 0)))).filter
      (· == KernelAxiom.piIntro)).length = 1 := by
  native_decide

/-! ## Canonical ordering

`sortAxioms` orders by `(category, index)` so output is stable
and grouped. -/

example :
    Term.sortAxioms [KernelAxiom.piElim, KernelAxiom.uWf, KernelAxiom.indForm]
      = [KernelAxiom.uWf, KernelAxiom.piElim, KernelAxiom.indForm] := by
  native_decide

example :
    Term.sortAxioms [KernelAxiom.quotLift, KernelAxiom.piForm, KernelAxiom.idJ]
      = [KernelAxiom.piForm, KernelAxiom.idJ, KernelAxiom.quotLift] := by
  native_decide

/-! ## Category grouping

Each axiom's `category` label groups it into one of the ten
Appendix-H sections. -/

example : KernelAxiom.category .uWf      = "H.1 Universes" := rfl
example : KernelAxiom.category .piForm   = "H.2 Pi" := rfl
example : KernelAxiom.category .indIntro = "H.4 Inductive" := rfl
example : KernelAxiom.category .idJ      = "H.6 Identity" := rfl
example : KernelAxiom.category .uEmit    = "H.10 Emit-table" := rfl

/-! ## Tag citations match Appendix H exactly

Spot-check a few citations to pin the 33-entry contract. -/

example : (KernelAxiom.tag .uWf).fst      = "H.1.1" := rfl
example : (KernelAxiom.tag .piElim).fst   = "H.2.3" := rfl
example : (KernelAxiom.tag .indIota).fst  = "H.4.4" := rfl
example : (KernelAxiom.tag .idJ).fst      = "H.6.3" := rfl
example : (KernelAxiom.tag .quotLift).fst = "H.7.3" := rfl
example : (KernelAxiom.tag .uEmit).fst    = "H.10.1" := rfl

end Tests.Kernel.AxiomWalker

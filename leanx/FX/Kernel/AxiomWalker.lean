import FX.Kernel.Term

/-!
# Kernel-axiom walker (F5)

Identifies which §31 Appendix-H kernel axioms a `Term` invokes by
its constructor-level shape.  Used by `fxi show-axioms SYMBOL
FILE.fx` to print the transitive axiom dependency closure of a
definition — the §1.2 "enumerable trusted base" made concrete.

## The §31 kernel axiom list

`fx_design.md` Appendix H enumerates 33 kernel axioms across ten
categories.  Every `Term` constructor corresponds to invoking one
or more of these axioms at the node's elaboration site:

```
H.1 Universes (5):      U-wf, U-hier, U-cumul, U-level, U-poly
H.2 Pi (3):             Pi-form, Pi-intro, Pi-elim
H.3 Sigma (3):          Σ-form, Σ-intro, Σ-elim
H.4 Inductive (4):      Ind-form, Ind-intro, Ind-elim, Ind-ι
H.5 Coinductive (4):    Coind-form, Coind-intro, Coind-elim, Coind-ν
H.6 Identity (3):       Id-form, Id-refl, Id-J
H.7 Quotient (3):       Quot-form, Quot-mk, Quot-lift
H.8 Grade algebra (5):  Grade-semiring-laws, Grade-subsumption,
                         Grade-division, Grade-zero, Grade-lattice
H.9 Subsumption (2):    T-conv, T-sub
H.10 Emit-table (1):    U-emit
```

Total: 33.  `AXIOMS.md`'s allowlist is 1-to-1 with this enum.

## What the walker identifies

The walker inspects kernel-term STRUCTURE and reports each axiom
whose corresponding kernel rule the term's elaboration would have
fired.  It does NOT inspect typing derivations — for a symbol
that survived elaboration, the axiom set is the union of axioms
corresponding to each constructor appearing in its type and body.

### What this captures

  * Every `Term.pi` node invokes `H.2.1 Pi-form` plus (recursively)
    the axioms of its domain and codomain.
  * Every `Term.lam` invokes `H.2.2 Pi-intro` plus recursively.
  * Every `Term.app` invokes `H.2.3 Pi-elim` plus recursively.
  * Every `Term.type` invokes `H.1.1 U-wf` (and `H.1.2 U-hier` if
    the universe level is non-zero — both are needed to form the
    next-level universe).
  * Every `Term.forallLevel` invokes `H.1.5 U-poly`.
  * `Term.sigma` / `Term.ind` / `Term.indRec` / `Term.id` /
    `Term.refl` / `Term.idJ` / `Term.quot` / `Term.quotMk` /
    `Term.quotLift` — one-to-one with Appendix H entries.
  * `Term.const` is opaque at this walker — the CLI walks the
    closure (via `GlobalEnv.closureConstRefs`) and computes
    axioms per referenced decl, then unions.

### What this does NOT capture (current limitations)

  * **H.8 Grade algebra** — these fire at every grade-carrying
    binder (Pi, Lam, Sigma).  Currently implicit in Pi-form etc.
    rather than reported separately.  Tracked explicitly requires
    per-grade inspection which would bloat output without adding
    information.
  * **H.9 T-conv / T-sub** — these fire at elaboration time
    (during conversion / subsumption checks) and leave no kernel-
    term residue, so the walker cannot detect their use.  They are
    treated as ALWAYS invoked whenever the elaborator ran — which
    it did for any symbol reaching the global env.  Reported in
    a summary line rather than per-term-node.
  * **H.10 U-emit** — fires only for atomic ops (§11.10) whose
    Phase-6 kernel terms are not yet part of `Term`.  The walker
    returns `[]` for Phase-1 terms.

### Soundness of the report

If the walker reports axiom set `S`, the symbol was accepted by
the kernel using at most `S` plus the universally-applied axioms
listed in "limitations".  If the walker reports empty, the symbol
depends on no Appendix-H axiom (only e.g. T-conv for
definitional equality — which does not appear in the enumerable
kernel trust base).

## Phase-1 caveats

The Lean 4 implementation (Phase 1/2) realizes most kernel rules
as `partial def` / `theorem` rather than as declared `axiom`s, so
`scripts/axiom-audit.sh` reports zero DECLARED axioms today.  The
walker's output represents LOGICAL axiom dependency — which rules
the elaborator invoked — independent of whether the corresponding
Lean code is an `axiom` or a computable `def`.  This is the
§1.2 "enumerable trusted base" sense.
-/

namespace FX.Kernel

/-- The 33-entry Appendix H kernel axiom list.  Constructor order
    mirrors H.1 through H.10 for predictable sorted output. -/
inductive KernelAxiom : Type where
  -- H.1 Universes (5)
  | uWf | uHier | uCumul | uLevel | uPoly
  -- H.2 Pi (3)
  | piForm | piIntro | piElim
  -- H.3 Sigma (3)
  | sigmaForm | sigmaIntro | sigmaElim
  -- H.4 Inductive (4)
  | indForm | indIntro | indElim | indIota
  -- H.5 Coinductive (4)
  | coindForm | coindIntro | coindElim | coindNu
  -- H.6 Identity (3)
  | idForm | idRefl | idJ
  -- H.7 Quotient (3)
  | quotForm | quotMk | quotLift
  -- H.8 Grade algebra (5)
  | gradeSemiringLaws | gradeSubsumption | gradeDivision | gradeZero | gradeLattice
  -- H.9 Subsumption / conversion (2)
  | tConv | tSub
  -- H.10 Emit-table (1)
  | uEmit
  deriving DecidableEq, Repr, BEq, Hashable

namespace KernelAxiom

/-- Appendix H citation tag — `(category, name)` pair for printing. -/
def tag : KernelAxiom → String × String
  | .uWf              => ("H.1.1", "U-wf")
  | .uHier            => ("H.1.2", "U-hier")
  | .uCumul           => ("H.1.3", "U-cumul")
  | .uLevel           => ("H.1.4", "U-level")
  | .uPoly            => ("H.1.5", "U-poly")
  | .piForm           => ("H.2.1", "Pi-form")
  | .piIntro          => ("H.2.2", "Pi-intro")
  | .piElim           => ("H.2.3", "Pi-elim")
  | .sigmaForm        => ("H.3.1", "Σ-form")
  | .sigmaIntro       => ("H.3.2", "Σ-intro")
  | .sigmaElim        => ("H.3.3", "Σ-elim")
  | .indForm          => ("H.4.1", "Ind-form")
  | .indIntro         => ("H.4.2", "Ind-intro")
  | .indElim          => ("H.4.3", "Ind-elim")
  | .indIota          => ("H.4.4", "Ind-ι")
  | .coindForm        => ("H.5.1", "Coind-form")
  | .coindIntro       => ("H.5.2", "Coind-intro")
  | .coindElim        => ("H.5.3", "Coind-elim")
  | .coindNu          => ("H.5.4", "Coind-ν")
  | .idForm           => ("H.6.1", "Id-form")
  | .idRefl           => ("H.6.2", "Id-refl")
  | .idJ              => ("H.6.3", "Id-J")
  | .quotForm         => ("H.7.1", "Quot-form")
  | .quotMk           => ("H.7.2", "Quot-mk")
  | .quotLift         => ("H.7.3", "Quot-lift")
  | .gradeSemiringLaws => ("H.8.1", "Grade-semiring-laws")
  | .gradeSubsumption  => ("H.8.2", "Grade-subsumption")
  | .gradeDivision     => ("H.8.3", "Grade-division")
  | .gradeZero         => ("H.8.4", "Grade-zero")
  | .gradeLattice      => ("H.8.5", "Grade-lattice")
  | .tConv            => ("H.9.1", "T-conv")
  | .tSub             => ("H.9.2", "T-sub")
  | .uEmit            => ("H.10.1", "U-emit")

/-- Total ordering by (category, index).  Used for sorted output. -/
def order : KernelAxiom → Nat
  | .uWf               =>  0 | .uHier             =>  1
  | .uCumul            =>  2 | .uLevel            =>  3
  | .uPoly             =>  4
  | .piForm            =>  5 | .piIntro           =>  6 | .piElim   =>  7
  | .sigmaForm         =>  8 | .sigmaIntro        =>  9 | .sigmaElim => 10
  | .indForm           => 11 | .indIntro          => 12
  | .indElim           => 13 | .indIota           => 14
  | .coindForm         => 15 | .coindIntro        => 16
  | .coindElim         => 17 | .coindNu           => 18
  | .idForm            => 19 | .idRefl            => 20 | .idJ    => 21
  | .quotForm          => 22 | .quotMk            => 23 | .quotLift => 24
  | .gradeSemiringLaws => 25 | .gradeSubsumption  => 26
  | .gradeDivision     => 27 | .gradeZero         => 28
  | .gradeLattice      => 29
  | .tConv             => 30 | .tSub              => 31
  | .uEmit             => 32

/-- Category label for group headers in pretty output. -/
def category : KernelAxiom → String
  | .uWf | .uHier | .uCumul | .uLevel | .uPoly                     => "H.1 Universes"
  | .piForm | .piIntro | .piElim                                   => "H.2 Pi"
  | .sigmaForm | .sigmaIntro | .sigmaElim                          => "H.3 Sigma"
  | .indForm | .indIntro | .indElim | .indIota                     => "H.4 Inductive"
  | .coindForm | .coindIntro | .coindElim | .coindNu               => "H.5 Coinductive"
  | .idForm | .idRefl | .idJ                                       => "H.6 Identity"
  | .quotForm | .quotMk | .quotLift                                => "H.7 Quotient"
  | .gradeSemiringLaws | .gradeSubsumption | .gradeDivision
  | .gradeZero | .gradeLattice                                     => "H.8 Grade algebra"
  | .tConv | .tSub                                                 => "H.9 Subsumption"
  | .uEmit                                                         => "H.10 Emit-table"

end KernelAxiom

namespace Term

/-! ## Shallow and deep axiom extraction from a Term

`ofHeadAxioms` returns the axioms invoked AT this term's root
node (not counting children).  `collectAxioms` walks the tree
unioning shallow axioms at every node. -/

/-- Axioms invoked at the `Term` constructor's head — no recursion
    into sub-terms.  Applied compositionally by `collectAxioms`. -/
def ofHeadAxioms : Term → List KernelAxiom
  | .var _            => []        -- bound var; no kernel rule at its head
  | .app _ _          => [.piElim]
  | .lam _ _ _        => [.piIntro]
  | .pi _ _ _ _       => [.piForm]
  | .sigma _ _ _      => [.sigmaForm]
  | .type _           => [.uWf, .uHier]  -- forming a universe invokes both
  | .forallLevel _    => [.uPoly]
  | .const _          => []        -- resolved by GlobalEnv walk, not here
  | .ind _ _          => [.indForm]
  | .ctor _ _ _ _     => [.indIntro]
  | .indRec _ _ _ _   => [.indElim]  -- ι fires only on concrete reductions
  | .coind _ _        => [.coindForm]
  | .coindUnfold _ _ _  => [.coindIntro]  -- Coind-intro (H.5.2)
  | .coindDestruct _ _ _ => [.coindElim, .coindNu]
                            -- Destructor application fires
                            -- Coind-elim (H.5.3) at typing and
                            -- Coind-ν (H.5.4) at reduction when
                            -- the target is an unfold.
  | .id _ _ _         => [.idForm]
  | .refl _           => [.idRefl]
  | .idJ _ _ _        => [.idJ]
  | .quot _ _         => [.quotForm]
  | .quotMk _ _       => [.quotMk]
  | .quotLift _ _ _   => [.quotLift]

/-- Deduplicating list union by structural equality on KernelAxiom. -/
def unionAxioms (acc : List KernelAxiom) (added : List KernelAxiom)
    : List KernelAxiom :=
  added.foldl (init := acc) fun accSoFar candidate =>
    if accSoFar.contains candidate then accSoFar else candidate :: accSoFar

/-- Collect every kernel axiom invoked anywhere in a term tree.
    Recursive; `partial def` because the Coind payload's
    structural termination isn't checked by default — all real
    terms are finite trees. -/
partial def collectAxioms : Term → List KernelAxiom := fun term =>
  let headAx := ofHeadAxioms term
  let childAxLists : List (List KernelAxiom) := childTerms term |>.map collectAxioms
  childAxLists.foldl (init := headAx) unionAxioms
where
  /-- Sub-terms of a Term node.  Lists all children so
      `collectAxioms` can recur. -/
  childTerms : Term → List Term
    | .var _                                   => []
    | .app f a                                 => [f, a]
    | .lam _grade dom body                     => [dom, body]
    | .pi _grade dom body _eff                 => [dom, body]
    | .sigma _grade dom body                   => [dom, body]
    | .type _                                  => []
    | .forallLevel body                        => [body]
    | .const _                                 => []
    | .ind _ args                              => args
    | .ctor _ _ typeArgs valueArgs             => typeArgs ++ valueArgs
    | .indRec _ motive methods target          => motive :: target :: methods
    | .coind _ coindArgs                       => coindArgs
    | .coindUnfold _ typeArgs arms             => typeArgs ++ arms
    | .coindDestruct _ _ target                => [target]
    | .id baseTy lhs rhs                       => [baseTy, lhs, rhs]
    | .refl witness                            => [witness]
    | .idJ motive base eqProof                 => [motive, base, eqProof]
    | .quot carrier rel                        => [carrier, rel]
    | .quotMk rel witness                      => [rel, witness]
    | .quotLift lifted respects target         => [lifted, respects, target]

/-- Sort a list of KernelAxioms by canonical order for
    deterministic output. -/
def sortAxioms (axioms : List KernelAxiom) : List KernelAxiom :=
  axioms.mergeSort (fun leftAx rightAx =>
    KernelAxiom.order leftAx ≤ KernelAxiom.order rightAx)

end Term

end FX.Kernel

import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfNormalFormCompiler

/-! # LinearAlgebra/InteractingHopfCompleteness — the IH_Q SYNTACTIC completeness
layer (WP-PROP-3 brick 12)

Brick 11 shipped the SEMANTIC IH_Q decision (`ihxNormalFormWordProblem`):
span-equal generator matrices are decided by the executable `ihqSpanEqB`.  This
brick upgrades toward the full SYNTACTIC word problem — two well-formed diagrams
whose denotations are span-equal are CONVERTIBLE in the committed IH presentation
congruence (`IhzConv`, the strongest committed congruence — whisker context plus
the fourteen scalar schemas).

## What lands

* LEG A — NF CANONICITY (denotational): `cvzNfCanonicalUpToSpan`.  Span-equal
  matrices compile (through the committed `ihxNormalFormCompiler`) to normal-form
  diagrams whose DENOTATIONS are themselves span-equal (`IhsRelEquiv` and the
  executable `ihqSpanEqB` both fire).  This is the maximal tractable fragment of
  LEG A: the NF compiler is canonical UP TO SPAN.  Fully proven, no wall.

* THE CONDITIONAL CAPSTONE: `cvzSyntacticCompletenessGivenReachability` and its
  biconditional companion `cvzWordProblemBiconditionalGivenReachability`.  GIVEN
  the committed owner-false reachability statement `ihzReachabilityStatement`
  (every span-equal WF-diagram pair is `IhzConv`), the executable span decision
  is EQUIVALENT to convertibility.  The `->` half (convertible ⇒ decision fires)
  is unconditional — it is the committed soundness bridge `ihzConvSpanEqB`; the
  `<-` half is exactly what reachability supplies.  This localizes the entire
  syntactic word problem to the single reachability obligation.

## What walls (LEG B and the syntactic half of LEG A)

The reachability obligation does NOT split into anything easier than itself here.
`cvzHasReductionToNormalForm := false` and
`cvzHasSpanEqualNormalFormsConvertible := false` name the two genuine walls:

  (LEG B, reduction) every WF diagram `IhzConv`-reduces to the NF of its
  denotation — the absorption-style layer induction pushing each generator
  through the accumulated span form via the A8/I3/I4 Frobenius-bimonoid moves and
  the fourteen `IhzRowMove` scalar schemas (census -> gate-refutation ->
  induction).  Absent from the committed code; `ihzReachabilityIsProven := false`.

  (LEG A, syntactic canonicity) span-equal NF diagrams are `IhzConv`.  Because the
  NF compiler is canonical only PER ROW LIST (span-equal matrices give DIFFERENT
  NF diagrams), closing this needs span-equal ⇒ equal canonical matrix, which is
  precisely `ihqRrefUniquenessStatement` (`ihqRrefUniquenessIsProven := false`),
  requiring a rank/independence/exchange apparatus absent from the `QnfRat` kit —
  MathComp `mxalgebra` never proves RREF uniqueness either.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural only;
no wildcard match arms over inductive scrutinees.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfCompleteness.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## LEG A — denotational normal-form canonicity -/

/-- LEG A (DENOTATIONAL NF CANONICITY): two span-equal generator matrices compile
through the committed NF compiler to well-formed normal-form diagrams whose
DENOTATIONS are span-equal — both the semantic `IhsRelEquiv` and the executable
`ihqSpanEqB` fire on the pair of NF denotations.  The NF compiler is canonical up
to span.  (The remaining gap to SYNTACTIC convertibility of the two NF diagrams is
the reachability wall — see `cvzHasSpanEqualNormalFormsConvertible`.) -/
theorem cvzNfCanonicalUpToSpan (domWidth codWidth : Nat)
    (rowsA rowsB : List (List QnfRat))
    (hRowsA : IhqAllWidth (domWidth + codWidth) rowsA)
    (hRowsB : IhqAllWidth (domWidth + codWidth) rowsB)
    (hSpan : ihqSpanEqB rowsA rowsB = true) :
    Exists fun nfA => Exists fun nfB =>
      (nfA.sourceArity = domWidth /\ ihsDiagramCodArity nfA = codWidth
        /\ IhsDiagramWF nfA
        /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote nfA) rowsA)
      /\ (nfB.sourceArity = domWidth /\ ihsDiagramCodArity nfB = codWidth
        /\ IhsDiagramWF nfB
        /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote nfB) rowsB)
      /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote nfA) (ihsDiagramDenote nfB)
      /\ ihqSpanEqB (ihsDiagramDenote nfA) (ihsDiagramDenote nfB) = true := by
  have hRowsEquiv : IhsRelEquiv domWidth codWidth rowsA rowsB :=
    (ihxSpanDecision domWidth codWidth rowsA rowsB hRowsA hRowsB).mpr hSpan
  cases ihxNormalFormCompiler domWidth codWidth rowsA hRowsA with
  | intro nfA hnfA =>
      cases ihxNormalFormCompiler domWidth codWidth rowsB hRowsB with
      | intro nfB hnfB =>
          have hNfEquiv : IhsRelEquiv domWidth codWidth
              (ihsDiagramDenote nfA) (ihsDiagramDenote nfB) :=
            ihsRelEquivTrans hnfA.right.right.right
              (ihsRelEquivTrans hRowsEquiv (ihsRelEquivSymm hnfB.right.right.right))
          have hAllNfA : IhqAllWidth (domWidth + codWidth) (ihsDiagramDenote nfA) := by
            have hRaw := ihsDiagramDenoteWidth nfA hnfA.right.right.left
            rw [hnfA.left, hnfA.right.left] at hRaw
            exact hRaw
          have hAllNfB : IhqAllWidth (domWidth + codWidth) (ihsDiagramDenote nfB) := by
            have hRaw := ihsDiagramDenoteWidth nfB hnfB.right.right.left
            rw [hnfB.left, hnfB.right.left] at hRaw
            exact hRaw
          exact Exists.intro nfA (Exists.intro nfB
            (And.intro hnfA (And.intro hnfB (And.intro hNfEquiv
              ((ihxSpanDecision domWidth codWidth (ihsDiagramDenote nfA)
                  (ihsDiagramDenote nfB) hAllNfA hAllNfB).mp hNfEquiv)))))

/-- DECIDED (LEG A): the NF compiler is canonical up to span — span-equal matrices
have span-equal NF denotations. -/
def cvzHasDenotationalNormalFormCanonicity : Bool := true

/-! ## The conditional capstone — syntactic completeness given reachability -/

/-- THE CONDITIONAL SYNTACTIC-COMPLETENESS CAPSTONE: GIVEN the committed
owner-false reachability statement (`ihzReachabilityStatement` — span-equal
WF diagrams are `IhzConv`), a `true` firing of the executable span decision on
two well-formed diagrams FORCES their convertibility in the strongest committed
IH congruence.  This routes the executable `ihqSpanEqB` decision through the
committed diagram word problem (`ihxDiagramWordProblem`) to the semantic
`IhsRelEquiv`, then discharges the syntactic step with the reachability
hypothesis.  Completeness of the IH_Q syntactic word problem MODULO the single
reachability wall. -/
theorem cvzSyntacticCompletenessGivenReachability
    (hReach : ihzReachabilityStatement)
    (firstDiagram secondDiagram : IhsDiagram)
    (hFirstWF : IhsDiagramWF firstDiagram) (hSecondWF : IhsDiagramWF secondDiagram)
    (hSource : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCod : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram)
    (hSpan : ihqSpanEqB (ihsDiagramDenote firstDiagram)
      (ihsDiagramDenote secondDiagram) = true) :
    IhzConv firstDiagram secondDiagram :=
  hReach firstDiagram secondDiagram hFirstWF hSecondWF hSource hCod
    ((ihxDiagramWordProblem firstDiagram secondDiagram hFirstWF hSecondWF
      hSource hCod).mpr hSpan)

/-- THE CONDITIONAL WORD-PROBLEM BICONDITIONAL: GIVEN reachability, convertibility
in the strongest committed IH congruence is EQUIVALENT to the executable span
decision.  The `->` half is unconditional (the committed soundness bridge
`ihzConvSpanEqB`); the `<-` half is the conditional capstone.  This is the full
IH_Q syntactic word problem, decided MODULO the reachability wall. -/
theorem cvzWordProblemBiconditionalGivenReachability
    (hReach : ihzReachabilityStatement)
    (firstDiagram secondDiagram : IhsDiagram)
    (hFirstWF : IhsDiagramWF firstDiagram) (hSecondWF : IhsDiagramWF secondDiagram)
    (hSource : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCod : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram) :
    IhzConv firstDiagram secondDiagram
      <-> ihqSpanEqB (ihsDiagramDenote firstDiagram)
            (ihsDiagramDenote secondDiagram) = true :=
  Iff.intro
    (fun hConv => ihzConvSpanEqB hConv)
    (fun hSpan => cvzSyntacticCompletenessGivenReachability hReach
      firstDiagram secondDiagram hFirstWF hSecondWF hSource hCod hSpan)

/-- DECIDED: the IH_Q syntactic word problem is decided MODULO reachability — the
conditional capstone and its biconditional companion ship. -/
def cvzHasConditionalWordProblem : Bool := true

/-! ## The walls — LEG B and the syntactic half of LEG A -/

/-- OWNER FALSE (LEG B, the reduction leg): no committed theorem states that every
well-formed diagram `IhzConv`-reduces to the normal form of its own denotation.
The residual is the absorption-style layer induction pushing each generator
through the accumulated span form via the A8/I3/I4 Frobenius-bimonoid moves and
the fourteen `IhzRowMove` scalar schemas, in the census -> gate-refutation ->
induction order.  Two burned attacks: (1) direct structural induction over
`firstDiagram.layers` stalls — the inductive step needs the generator absorbed
into the accumulated span form, which is a whisker-context rewrite `IhzConv` can
witness but whose confluence is unestablished; (2) reduce-via-the-compiler stalls
because the compiler NF of `denote diagram` is built from the DENOTATION MATRIX,
not the layers, so there is no structural handle relating the two syntactically.
Coincides with the committed `ihzReachabilityIsProven := false`. -/
def cvzHasReductionToNormalForm : Bool := false

/-- OWNER FALSE (LEG A, the syntactic canonicity leg): span-equal normal-form
diagrams are NOT proven `IhzConv`.  `cvzNfCanonicalUpToSpan` closes this
DENOTATIONALLY (the NF denotations are span-equal), but the SYNTACTIC step fails:
the NF compiler is canonical only per ROW LIST, so span-equal matrices produce
DIFFERENT NF diagrams.  Closing this needs span-equal ⇒ equal canonical matrix —
exactly `ihqRrefUniquenessStatement` (`ihqRrefUniquenessIsProven := false`) —
which requires a rank/independence/exchange apparatus absent from the `QnfRat`
kit (MathComp `mxalgebra` never proves RREF uniqueness either).  Two burned
attacks: (1) `ihqRref`-canonicalize both then compare bytes — blocked, uniqueness
is owner-false; (2) rewrite one NF into the other by re-running the compiler on
the shared span — no shared canonical matrix exists without leg (1). -/
def cvzHasSpanEqualNormalFormsConvertible : Bool := false

/-- OWNER FALSE (the unconditional capstone): the IH_Q syntactic completeness
`ihqSpanEqB (denote d1) (denote d2) = true -> IhzConv d1 d2` is NOT proven
unconditionally — only MODULO reachability (see
`cvzSyntacticCompletenessGivenReachability`).  It is the conjunction of the two
walls above (reduction + syntactic canonicity), equivalently the committed
`ihzReachabilityStatement` (`ihzReachabilityIsProven := false`). -/
def cvzHasSyntacticCompleteness : Bool := false

/-! ## Ground fires -/

/-- The committed NF diagram of the single line `[[1,2]]` at boundary `(1,1)`
(one row-cons onto the zero relation). -/
def cvzNormalFormLineOneTwo : IhsDiagram :=
  ihxRowConsDiagram [qnfOne] [ihsScalarTwo] (ihzZeroRelationDiagram 1 1).layers

/-- The committed NF diagram of the DIFFERENT line `[[2,4]]` at boundary `(1,1)` —
span-equal to `[[1,2]]` but a distinct row list, so a distinct NF diagram. -/
def cvzNormalFormLineTwoFour : IhsDiagram :=
  ihxRowConsDiagram [ihsScalarTwo] [ihzScalarFour] (ihzZeroRelationDiagram 1 1).layers

/-- The committed NF diagram of the line `[[1,3]]` — a DIFFERENT subspace, for the
FALSE control. -/
def cvzNormalFormLineOneThree : IhsDiagram :=
  ihxRowConsDiagram [qnfOne] [ihsScalarThree] (ihzZeroRelationDiagram 1 1).layers

set_option maxHeartbeats 8000000 in
/-- FIRE (NF correctness): the NF diagram of `[[1,2]]` denotes exactly the span of
`[[1,2]]` — the kernel span decision fires `true`. -/
theorem cvzFireNfLineCorrect :
    ihqSpanEqB (ihsDiagramDenote cvzNormalFormLineOneTwo)
      [[qnfOne, ihsScalarTwo]] = true := rfl

set_option maxHeartbeats 8000000 in
/-- FIRE (LEG A — SPAN-EQUAL PAIR HAS EQUAL CANONICAL NF): the two DISTINCT NF
diagrams of the span-equal matrices `[[1,2]]` and `[[2,4]]` have span-equal
DENOTATIONS — the kernel decides their NF denotations equal.  This is the
denotational NF canonicity `cvzNfCanonicalUpToSpan` on the nose. -/
theorem cvzFireNfDenotationsSpanEqual :
    ihqSpanEqB (ihsDiagramDenote cvzNormalFormLineOneTwo)
      (ihsDiagramDenote cvzNormalFormLineTwoFour) = true := rfl

set_option maxHeartbeats 8000000 in
/-- FIRE (FALSE control): the NF diagrams of `[[1,2]]` and `[[1,3]]` denote
DIFFERENT lines — the kernel span decision refutes. -/
theorem cvzFireNfDenotationsSpanUnequalControl :
    ihqSpanEqB (ihsDiagramDenote cvzNormalFormLineOneTwo)
      (ihsDiagramDenote cvzNormalFormLineOneThree) = false := rfl

set_option maxHeartbeats 8000000 in
/-- CONTENT FIRE (routes through `cvzNfCanonicalUpToSpan`, not a bare span `rfl`):
the span-equal pair `[[1,2]]`, `[[2,4]]` at boundary `(1,1)` yields, through the
committed NF compiler and the span decision, two well-formed NF diagrams with
span-equal denotations. -/
theorem cvzFireContentNfCanonicity :
    Exists fun nfA => Exists fun nfB =>
      (nfA.sourceArity = 1 /\ ihsDiagramCodArity nfA = 1 /\ IhsDiagramWF nfA
        /\ IhsRelEquiv 1 1 (ihsDiagramDenote nfA) [[qnfOne, ihsScalarTwo]])
      /\ (nfB.sourceArity = 1 /\ ihsDiagramCodArity nfB = 1 /\ IhsDiagramWF nfB
        /\ IhsRelEquiv 1 1 (ihsDiagramDenote nfB) [[ihsScalarTwo, ihzScalarFour]])
      /\ IhsRelEquiv 1 1 (ihsDiagramDenote nfA) (ihsDiagramDenote nfB)
      /\ ihqSpanEqB (ihsDiagramDenote nfA) (ihsDiagramDenote nfB) = true :=
  cvzNfCanonicalUpToSpan 1 1 [[qnfOne, ihsScalarTwo]] [[ihsScalarTwo, ihzScalarFour]]
    (IhqAllWidth.cons rfl IhqAllWidth.nil)
    (IhqAllWidth.cons rfl IhqAllWidth.nil)
    rfl

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfNormalFormCompiler

/-! # LinearAlgebra/InteractingHopfCompleteness — the IH_Q syntactic completeness layer

The IH_Q syntactic word problem asks whether two well-formed diagrams with
span-equal denotations are convertible in the strongest committed IH congruence
(`IhzConv`).  Two results land: denotational NF canonicity
(`cvzNfCanonicalUpToSpan`) — span-equal generator matrices compile through the
committed `ihxNormalFormCompiler` to well-formed NF diagrams whose denotations are
again span-equal, so the compiler is canonical up to span; and the conditional
capstone (`cvzSyntacticCompletenessGivenReachability` and its biconditional
companion) — given the committed reachability statement, the executable span
decision is equivalent to convertibility, localizing the whole word problem to that
one obligation.  Unconditional completeness stays open, holding only modulo
reachability — see `cvzHasSyntacticCompleteness`.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural only;
no wildcard match arms over inductive scrutinees.  Per-declaration gate in the
audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Denotational normal-form canonicity -/

/-- Denotational NF canonicity: two span-equal generator matrices compile through
the committed NF compiler to well-formed normal-form diagrams whose denotations are
span-equal — both the semantic `IhsRelEquiv` and the executable `ihqSpanEqB` fire on
the pair of NF denotations, so the NF compiler is canonical up to span.  The
remaining gap to syntactic convertibility of the two NF diagrams is the
reachability wall. -/
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

/-! ## The conditional capstone — syntactic completeness given reachability -/

/-- The conditional syntactic-completeness capstone: given the committed
reachability statement (`ihzReachabilityStatement` — span-equal WF diagrams are
`IhzConv`), a `true` span decision on two well-formed diagrams forces their
convertibility in the strongest committed IH congruence, routing `ihqSpanEqB`
through the committed diagram word problem (`ihxDiagramWordProblem`) to
`IhsRelEquiv` and discharging the syntactic step with reachability. -/
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

/-- The conditional word-problem biconditional: given reachability, convertibility
in the strongest committed IH congruence is equivalent to the executable span
decision.  The `->` half is unconditional (the committed soundness bridge
`ihzConvSpanEqB`); the `<-` half is the conditional capstone — the full IH_Q
syntactic word problem, decided modulo the reachability wall. -/
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

/-- Given the reachability statement, convertibility in the strongest committed IH
congruence is equivalent to the executable span decision (the conditional capstone
and its biconditional companion); this brick also ships denotational NF canonicity,
namely that span-equal matrices have span-equal NF denotations. -/
def cvzHasConditionalWordProblem : Bool := true

/-! ## The walls — reduction and syntactic canonicity -/

/-- Unconditional syntactic completeness `ihqSpanEqB (denote d1) (denote d2) = true
-> IhzConv d1 d2` is open.  It is the conjunction of the reduction leg — every WF
diagram `IhzConv`-reduces to the NF of its denotation, an absorption-style layer
induction whose confluence is unestablished — and the syntactic-canonicity leg —
span-equal NF diagrams are `IhzConv`, which needs RREF uniqueness absent from the
`QnfRat` kit.  It holds only modulo the reachability statement. -/
def cvzHasSyntacticCompleteness : Bool := false

/-! ## Ground fires -/

/-- The committed NF diagram of the single line `[[1,2]]` at boundary `(1,1)` (one
row-cons onto the zero relation). -/
def cvzNormalFormLineOneTwo : IhsDiagram :=
  ihxRowConsDiagram [qnfOne] [ihsScalarTwo] (ihzZeroRelationDiagram 1 1).layers

/-- The committed NF diagram of the different line `[[2,4]]` at boundary `(1,1)` —
span-equal to `[[1,2]]` but a distinct row list, hence a distinct NF diagram. -/
def cvzNormalFormLineTwoFour : IhsDiagram :=
  ihxRowConsDiagram [ihsScalarTwo] [ihzScalarFour] (ihzZeroRelationDiagram 1 1).layers

/-- The committed NF diagram of the line `[[1,3]]` — a different subspace, for the
false control. -/
def cvzNormalFormLineOneThree : IhsDiagram :=
  ihxRowConsDiagram [qnfOne] [ihsScalarThree] (ihzZeroRelationDiagram 1 1).layers

set_option maxHeartbeats 8000000 in
/-- NF correctness: the NF diagram of `[[1,2]]` denotes exactly the span of `[[1,2]]`;
the kernel span decision fires `true`. -/
theorem cvzFireNfLineCorrect :
    ihqSpanEqB (ihsDiagramDenote cvzNormalFormLineOneTwo)
      [[qnfOne, ihsScalarTwo]] = true := rfl

set_option maxHeartbeats 8000000 in
/-- Span-equal pair has equal canonical NF: the two distinct NF diagrams of the
span-equal matrices `[[1,2]]` and `[[2,4]]` have span-equal denotations, the kernel
deciding their NF denotations equal — denotational NF canonicity
(`cvzNfCanonicalUpToSpan`) on the nose. -/
theorem cvzFireNfDenotationsSpanEqual :
    ihqSpanEqB (ihsDiagramDenote cvzNormalFormLineOneTwo)
      (ihsDiagramDenote cvzNormalFormLineTwoFour) = true := rfl

set_option maxHeartbeats 8000000 in
/-- False control: the NF diagrams of `[[1,2]]` and `[[1,3]]` denote different lines;
the kernel span decision refutes. -/
theorem cvzFireNfDenotationsSpanUnequalControl :
    ihqSpanEqB (ihsDiagramDenote cvzNormalFormLineOneTwo)
      (ihsDiagramDenote cvzNormalFormLineOneThree) = false := rfl

set_option maxHeartbeats 8000000 in
/-- Content fire routing through `cvzNfCanonicalUpToSpan` (not a bare span `rfl`):
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

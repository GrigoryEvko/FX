import FX1Poly.Polygraph.Omega.RelProp.BooleanRelationProp

/-! # Polygraph/Omega/Markov/FreeCopyDiscard — the free copy-discard (CD) / Markov PROP, decided by
Boolean matrices, with the deterministic (function) sub-PROP carved out and the general Markov
completeness WALLED (WP-MARKOV)

GREENFIELD-BY-REUSE LAW: this file adds the copy-discard / Markov LAYER on top of the already-committed
Carboni-Walters relation kit `FX1Poly.Polygraph.Omega.RelProp` (the `BooleanRelationProp` file).  It
does NOT re-derive any matrix arithmetic, the diagram carrier, the congruence, the soundness lift, or
the decision — those ARE the CD word problem for the relation model and are reused verbatim.  What is
GENUINELY NEW here:

* the CD/Markov RE-TAGGING of the carrier, congruence, denotation and decision under copy-discard names
  (`CdDiagram`, `CdConv`, `denoteCd`, `decideCdConv`), so the free-CD word problem reads in Markov
  vocabulary;
* the DETERMINISTIC (total-function) sub-PROP as a decidable refinement of the decided relation model:
  a Boolean matrix is a FUNCTION matrix iff every source column carries EXACTLY ONE `true` (the graph
  of a finite function `[source] -> [target]`).  The comonoid generators split precisely: merge, create,
  swap and identities ARE deterministic (they generate the finite-function PROP); copy and discard are
  NOT (copy has two `true`s in its single column, discard has zero) — the exact reason copy/discard are
  the non-cartesian half.  Determinism is proved to be a property of the DENOTATION, hence invariant
  under `CdConv` (`cdwDeterminismRespectsCdConv`) — the Markov-category fact that determinism is
  intrinsic, not syntactic.

## Why this is the free CD category, not just relations

A CD category (Cho-Jacobs / Fritz Markov categories without the discard-natural / affine axiom is a
"copy-discard category"; adding discard-naturality of every morphism gives a Markov category) is a
symmetric monoidal category in which every object carries a COMMUTATIVE COMONOID (copy `delta`,
discard `epsilon`) that is coherent with the monoidal structure.  That is EXACTLY the comonoid +
symmetry + naturality fragment of the Carboni-Walters presentation reused here: `fromCopyCoassocRow`,
`fromCopyLeftCounitRow`/`fromCopyRightCounitRow` (counit via discard), `fromCopyCocommRow`
(cocommutativity via swap), and the bialgebra/naturality squares `fromCopyAfterMergeRow`,
`fromDiscardAfterMergeRow`.  The Boolean (relation) model `Rel` is the free CD category on one object
where copy is the diagonal and discard is the terminal map; the DETERMINISTIC morphisms are the
functions.  A general MARKOV category quotient (probabilistic / row-stochastic channels reconstructed
from their matrix) is the deep extension — WALLED below.

## THE SOURCES

* [ChoJacobs2019] K. Cho, B. Jacobs, *Disintegration and Bayesian inversion via string diagrams*, MSCS
  29 (2019): CD categories = symmetric monoidal + coherent commutative comonoid on every object;
  deterministic = copy-preserving.
* [Fritz2020] T. Fritz, *A synthetic approach to Markov kernels, conditional independence and theorems
  on sufficient statistics*, Adv. Math. 370 (2020): Markov categories; `Rel` and `FinStoch` as the
  possibilistic / probabilistic instances; deterministic morphisms = the comonoid homomorphisms.
* [CarboniWalters1987] cartesian bicategories: `Rel` as the walking cartesian bicategory; maps = total
  single-valued relations = functions.
* [Lack2004] `Rel = comonoid o monoid`; the monoid part (`merge`, `create`) generates finite functions.

Raw Lean 4 + Init only; zero-axiom; structural recursion on `Nat` bounds only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` witness. -/

namespace FX1Poly.Polygraph.Omega.Markov

open FX1Poly.Polygraph.Omega.RelProp

/-! ## Section 1 — the CD / Markov re-tagging of the reused relation kit (T1) -/

/-- A CD (copy-discard) string diagram `sourceArity -> targetArity`.  This IS the reused seven-generator
Carboni-Walters carrier: `identityWires`, `composeSequential`, `tensorParallel`, plus the generators
`copyGen : 1 -> 2` (the comonoid comultiplication `delta`), `discardGen : 1 -> 0` (the counit
`epsilon`), `swapGen : 2 -> 2` (the symmetry), and the monoid duals `mergeGen`/`createGen`, with
`capGen`/`cupGen`.  A diagram `m -> n` denotes an `n x m` Boolean matrix. -/
abbrev CdDiagram : Nat -> Nat -> Type := RelDiagram

/-- The CD congruence: the smallest congruence containing the commutative-comonoid rows (copy
coassociativity, copy counit via discard, copy cocommutativity via swap), the bialgebra/naturality
squares of copy and discard against merge and create, the symmetry rows, and the strict symmetric
monoidal structure.  This IS the reused `RelConv`. -/
abbrev CdConv {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : CdDiagram sourceArity targetArity) : Prop :=
  RelConv leftDiagram rightDiagram

/-- The matrix denotation of a CD diagram into `Mat(Bool)`: copy denotes the diagonal-duplicating
column `[[1],[1]]`, discard the empty/terminal row, merge the row `[[1,1]]`, and the structural
constructors the identity matrix, the OR-AND product, and the block-diagonal direct sum.  Reuses the
relation denotation verbatim. -/
abbrev denoteCd {sourceArity targetArity : Nat}
    (diagram : CdDiagram sourceArity targetArity) : BoolMatrixEntries :=
  denoteBoolEntries diagram

/-! ## Section 2 — CD-axiom soundness (T2): the comonoid + naturality rows and the congruence lift -/

/-- Copy is COASSOCIATIVE: `delta ; (delta (x) id) = delta ; (id (x) delta)` as equal Boolean
matrices.  Reused per-row fire. -/
theorem cdwCopyCoassocSound :
    doBoolEntriesAgreeUpTo 3 1 (denoteCd copyCoassocLeftSide) (denoteCd copyCoassocRightSide) = true :=
  copyCoassocRowIsSound

/-- Copy LEFT COUNIT via discard: `delta ; (epsilon (x) id) = id`. -/
theorem cdwCopyLeftCounitSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteCd copyLeftCounitLeftSide) (denoteCd copyLeftCounitRightSide)
      = true :=
  copyLeftCounitRowIsSound

/-- Copy RIGHT COUNIT via discard: `delta ; (id (x) epsilon) = id`. -/
theorem cdwCopyRightCounitSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteCd copyRightCounitLeftSide) (denoteCd copyRightCounitRightSide)
      = true :=
  copyRightCounitRowIsSound

/-- Copy COCOMMUTATIVITY via swap: `delta ; tau = delta`. -/
theorem cdwCopyCocommSound :
    doBoolEntriesAgreeUpTo 2 1 (denoteCd copyCocommLeftSide) (denoteCd copyCocommRightSide) = true :=
  copyCocommRowIsSound

/-- Copy is NATURAL against merge (the bialgebra square): `mu ; delta = (delta (x) delta) ; window ;
(mu (x) mu)`. -/
theorem cdwCopyAfterMergeSound :
    doBoolEntriesAgreeUpTo 2 2 (denoteCd copyAfterMergeLeftSide) (denoteCd copyAfterMergeRightSide)
      = true :=
  copyAfterMergeRowIsSound

/-- Discard is NATURAL against merge: `mu ; epsilon = epsilon (x) epsilon`. -/
theorem cdwDiscardAfterMergeSound :
    doBoolEntriesAgreeUpTo 0 2 (denoteCd discardAfterMergeLeftSide)
      (denoteCd discardAfterMergeRightSide) = true :=
  discardAfterMergeRowIsSound

/-- The Bool-specific SPECIAL FROBENIUS law `delta ; mu = id` (unsound over N, where it doubles). -/
theorem cdwSpecialFrobeniusSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteCd specialFrobeniusLeftSide)
      (denoteCd specialFrobeniusRightSide) = true :=
  specialFrobeniusRowIsSound

/-- THE CD-CONGRUENCE SOUNDNESS LIFT (T2): convertible CD diagrams denote equal Boolean matrices, by
induction over `CdConv` (matrix functoriality).  Reused congruence-closure lift. -/
theorem cdConvImpliesDenotationsAgree {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : CdDiagram sourceArity targetArity}
    (areConvertible : CdConv leftDiagram rightDiagram) :
    doBoolEntriesAgreeUpTo targetArity sourceArity
      (denoteCd leftDiagram) (denoteCd rightDiagram) = true :=
  convertibleRelDiagramsDenoteEqualBoolMatrices areConvertible

/-! ## Section 3 — the decision (T3) -/

/-- THE DECISION: two CD diagrams are declared convertible iff their Boolean matrices agree on the full
`targetArity x sourceArity` rectangle.  Reused Boolean-matrix-equality decision. -/
def decideCdConv {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : CdDiagram sourceArity targetArity) : Bool :=
  decideRelConvBool leftDiagram rightDiagram

/-- SOUND DIRECTION: convertible CD diagrams pass the decision. -/
theorem decisionIsImpliedByCdConv {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : CdDiagram sourceArity targetArity}
    (areConvertible : CdConv leftDiagram rightDiagram) :
    decideCdConv leftDiagram rightDiagram = true :=
  decisionIsImpliedByRelConv areConvertible

/-- THE NEGATIVE DECISION: CD diagrams whose Boolean matrices DIFFER are NOT convertible (soundness
contraposed) — a `false` matrix comparison is a machine-checked refutation of CD-convertibility. -/
theorem notCdConvOfDistinctMatrices {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : CdDiagram sourceArity targetArity)
    (doMatricesDiffer : decideCdConv leftDiagram rightDiagram = false) :
    CdConv leftDiagram rightDiagram -> False :=
  notRelConvOfDistinctBoolMatrices leftDiagram rightDiagram doMatricesDiffer

/-! ## Section 4 — the DETERMINISTIC (finite-function) sub-PROP as a decidable refinement (T3, the
closeable Markov content) -/

/-- Count the `true`s of a Boolean column function strictly below a bound (structural on the bound). -/
def countTrueBelow (columnAt : Nat -> Bool) : Nat -> Nat
  | 0 => 0
  | boundPred + 1 => countTrueBelow columnAt boundPred + cond (columnAt boundPred) 1 0

/-- Is column `colIndex` (read over `rowCount` rows) the graph of a function value — i.e. does it carry
EXACTLY ONE `true`?  This is the total-single-valued test on one input wire. -/
def isFunctionColumn (entries : BoolMatrixEntries) (rowCount colIndex : Nat) : Bool :=
  Nat.beq (countTrueBelow (fun rowIndex => entries rowIndex colIndex) rowCount) 1

/-- Do all source columns below the bound pass the function-column test (structural on the bound)? -/
def allFunctionColumnsBelow (entries : BoolMatrixEntries) (rowCount : Nat) : Nat -> Bool
  | 0 => true
  | colBoundPred + 1 =>
      allFunctionColumnsBelow entries rowCount colBoundPred
        && isFunctionColumn entries rowCount colBoundPred

/-- A Boolean matrix is a FUNCTION (deterministic) matrix on its `rowCount x colCount` rectangle iff
every source column carries exactly one `true` — the graph of a finite function `[colCount] ->
[rowCount]`. -/
def cdwIsDeterministicMatrix (entries : BoolMatrixEntries) (rowCount colCount : Nat) : Bool :=
  allFunctionColumnsBelow entries rowCount colCount

/-- A CD diagram is DETERMINISTIC iff its denotation is a function matrix — the Markov-category notion
of a deterministic morphism, here decided by the reused matrix engine. -/
def cdwIsDeterministic {sourceArity targetArity : Nat}
    (diagram : CdDiagram sourceArity targetArity) : Bool :=
  cdwIsDeterministicMatrix (denoteCd diagram) targetArity sourceArity

/-! ### Determinism is a property of the denotation (intrinsic), hence `CdConv`-invariant -/

/-- `countTrueBelow` depends only on the column values below the bound. -/
theorem countTrueBelowRespectsPointwise (firstColumnAt secondColumnAt : Nat -> Bool) :
    (bound : Nat) ->
    (∀ rowIndex, rowIndex < bound -> firstColumnAt rowIndex = secondColumnAt rowIndex) ->
    countTrueBelow firstColumnAt bound = countTrueBelow secondColumnAt bound
  | 0, _ => rfl
  | boundPred + 1, agreeBelow => by
      have tailAgrees := countTrueBelowRespectsPointwise firstColumnAt secondColumnAt boundPred
        (fun rowIndex isBelow => agreeBelow rowIndex (Nat.le.step isBelow))
      show (countTrueBelow firstColumnAt boundPred + cond (firstColumnAt boundPred) 1 0)
        = (countTrueBelow secondColumnAt boundPred + cond (secondColumnAt boundPred) 1 0)
      rw [tailAgrees, agreeBelow boundPred (Nat.lt_succ_self boundPred)]

/-- `allFunctionColumnsBelow` depends only on the entries inside its `rowCount x colCount` rectangle. -/
theorem allFunctionColumnsRespectsPointwise (leftEntries rightEntries : BoolMatrixEntries)
    (rowCount : Nat) :
    (colCount : Nat) ->
    (∀ rowIndex colIndex, rowIndex < rowCount -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) ->
    allFunctionColumnsBelow leftEntries rowCount colCount
      = allFunctionColumnsBelow rightEntries rowCount colCount
  | 0, _ => rfl
  | colBoundPred + 1, agreeInRectangle => by
      have tailAgrees := allFunctionColumnsRespectsPointwise leftEntries rightEntries rowCount
        colBoundPred
        (fun rowIndex colIndex isRowBelow isColBelow =>
          agreeInRectangle rowIndex colIndex isRowBelow (Nat.le.step isColBelow))
      have headAgrees : isFunctionColumn leftEntries rowCount colBoundPred
          = isFunctionColumn rightEntries rowCount colBoundPred := by
        show Nat.beq (countTrueBelow (fun rowIndex => leftEntries rowIndex colBoundPred) rowCount) 1
          = Nat.beq (countTrueBelow (fun rowIndex => rightEntries rowIndex colBoundPred) rowCount) 1
        rw [countTrueBelowRespectsPointwise
          (fun rowIndex => leftEntries rowIndex colBoundPred)
          (fun rowIndex => rightEntries rowIndex colBoundPred) rowCount
          (fun rowIndex isRowBelow =>
            agreeInRectangle rowIndex colBoundPred isRowBelow (Nat.lt_succ_self colBoundPred))]
      show (allFunctionColumnsBelow leftEntries rowCount colBoundPred
          && isFunctionColumn leftEntries rowCount colBoundPred)
        = (allFunctionColumnsBelow rightEntries rowCount colBoundPred
          && isFunctionColumn rightEntries rowCount colBoundPred)
      rw [tailAgrees, headAgrees]

/-- DETERMINISM IS INTRINSIC: `CdConv`-convertible diagrams have the SAME determinism verdict — being
a function is a property of the underlying relation, not of the string diagram presenting it.  This is
the Markov-category coherence that "deterministic" is well-defined on morphisms. -/
theorem cdwDeterminismRespectsCdConv {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : CdDiagram sourceArity targetArity}
    (areConvertible : CdConv leftDiagram rightDiagram) :
    cdwIsDeterministic leftDiagram = cdwIsDeterministic rightDiagram := by
  have agreePointwise := pointwiseOfAgreeUpTo targetArity sourceArity
    (denoteCd leftDiagram) (denoteCd rightDiagram) (cdConvImpliesDenotationsAgree areConvertible)
  show allFunctionColumnsBelow (denoteCd leftDiagram) targetArity sourceArity
    = allFunctionColumnsBelow (denoteCd rightDiagram) targetArity sourceArity
  exact allFunctionColumnsRespectsPointwise _ _ targetArity sourceArity
    (fun rowIndex colIndex isRowInRange isColInRange =>
      agreePointwise rowIndex colIndex isRowInRange isColInRange)

/-! ### Which generators are deterministic — the function / non-function split -/

/-- merge `mu : 2 -> 1` IS deterministic: matrix `[[1,1]]`, each source column has exactly one `true`
(it is the constant finite function `[2] -> [1]`). -/
theorem cdwMergeIsDeterministic : cdwIsDeterministic RelDiagram.mergeGen = true := rfl

/-- create `eta : 0 -> 1` IS deterministic: the unique function `empty -> [1]` (vacuously — zero
columns). -/
theorem cdwCreateIsDeterministic : cdwIsDeterministic RelDiagram.createGen = true := rfl

/-- swap `tau : 2 -> 2` IS deterministic: the transposition function. -/
theorem cdwSwapIsDeterministic : cdwIsDeterministic RelDiagram.swapGen = true := rfl

/-- the identity on two wires IS deterministic. -/
theorem cdwIdentityIsDeterministic : cdwIsDeterministic (RelDiagram.identityWires 2) = true := rfl

/-- copy `delta : 1 -> 2` is NOT deterministic: its single source column has TWO `true`s (both output
wires) — the exact non-cartesian content of comultiplication. -/
theorem cdwCopyIsNotDeterministic : cdwIsDeterministic RelDiagram.copyGen = false := rfl

/-- discard `epsilon : 1 -> 0` is NOT deterministic: its source column has ZERO `true`s (no total
function `[1] -> empty`). -/
theorem cdwDiscardIsNotDeterministic : cdwIsDeterministic RelDiagram.discardGen = false := rfl

/-- DETERMINISM IS SEMANTIC, NOT SYNTACTIC: although copy alone is non-deterministic, the composite
`delta ; mu` (special Frobenius) denotes the identity `[[1]]`, which IS a function matrix — so the
composite is deterministic.  Witnesses that `cdwIsDeterministic` reads the denotation, matching
`cdwDeterminismRespectsCdConv`. -/
theorem cdwSpecialFrobeniusIsDeterministic :
    cdwIsDeterministic specialFrobeniusLeftSide = true := rfl

/-! ## Section 5 — the MARKOV COMPLETENESS WALL (T4) -/

/-- THE MARKOV COMPLETENESS STATEMENT (the converse of the CD decision): equal Boolean matrices imply
`CdConv`-convertibility.  Stated as the named target; WALLED below. -/
def markovCompletenessStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (leftDiagram rightDiagram : CdDiagram sourceArity targetArity),
    decideCdConv leftDiagram rightDiagram = true -> CdConv leftDiagram rightDiagram

/-- THE DETERMINISTIC-RECONSTRUCTION STATEMENT: every function (deterministic) matrix is the denotation
of SOME CD diagram of the matching arity.  The concrete shape of the obstruction: building the
canonical function diagram from a `[source] -> [target]` graph.  Stated; used only to name the wall's
obstruction. -/
def markovDeterministicReconstructionStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (channelMatrix : BoolMatrixEntries),
    cdwIsDeterministicMatrix channelMatrix targetArity sourceArity = true ->
      ∃ diagram : CdDiagram sourceArity targetArity,
        doBoolEntriesAgreeUpTo targetArity sourceArity (denoteCd diagram) channelMatrix = true

/-- OWNER MARKER (false): the general Markov-category / CD word-problem COMPLETENESS is NOT proven here.

WHAT IS WALLED: the converse `equal matrix => CdConv` (`markovCompletenessStatement`), and its deep
extension to reconstructing a canonical CD diagram from a general channel matrix
(`markovDeterministicReconstructionStatement`) — the surjectivity-onto-matrices half of the word
problem.  What DID land: soundness (`cdConvImpliesDenotationsAgree`) and the two-sided decision
(`decideCdConv` with `notCdConvOfDistinctMatrices`), plus the deterministic sub-PROP carve-out fully
decided.

TWO BURNED ATTACKS:
* Attack 1 (relational-fragment completeness, then lift): the Boolean relation fragment's OWN
  completeness is already an owner-false wall in the reused kit
  (`FX1Poly.Polygraph.Omega.RelProp.rcwHasCarboniWaltersCompleteness := false`), blocked on the
  canonical-reduction lemma `d ~ normalForm d` — a terminating Squier-style fan-core rewrite completion
  that is NOT built.  The Markov layer sits strictly ABOVE the relation layer (deterministic morphisms
  are a refinement of relations), so it inherits that exact unbuilt completion: no CD-level completeness
  can be closed while the relation-level one is open.
* Attack 2 (stochastic / FinStoch reconstruction over a different rig): a GENERAL Markov category is
  `FinStoch` — row-stochastic rational (`QnfRat` row-sum-1) matrices, not Boolean ones — whose word
  problem needs the `Mat(Q+)` carrier with row-normalisation, NOT the idempotent Boolean carrier used
  here.  The sibling N lane already REFUTED current-presentation completeness for its matrix model
  (its `matNatCompletenessStatementIsRefuted`: distinct-but-equal-matrix diagrams unjoined by the
  present rows because the unit-coherence rows are missing), so channel reconstruction is delicate
  presentation-completion work — provably not a quick converse — and the ordered-support canonical form
  for a stochastic channel is unbuilt. -/
def cdwHasMarkovCompleteness : Bool := false

/-! ## Section 6 — ground fires (T5) -/

/-- FIRE 1 (counit law): `delta ; (epsilon (x) id) = id` — copy-then-discard-one-leg is the identity
wire; decides `true` and is `CdConv`-convertible. -/
theorem fireCopyDiscardCounitLaw :
    decideCdConv copyLeftCounitLeftSide copyLeftCounitRightSide = true
      ∧ CdConv copyLeftCounitLeftSide copyLeftCounitRightSide :=
  ⟨rfl, RelConv.fromCopyLeftCounitRow⟩

/-- FIRE 2 (coassociativity): `delta ; (delta (x) id)` and `delta ; (id (x) delta)` denote EQUAL
Boolean matrices on the `3 x 1` rectangle. -/
theorem fireCopyCoassocMatricesEqual :
    decideCdConv copyCoassocLeftSide copyCoassocRightSide = true := rfl

/-- FIRE 3 (a convertible pair decides equal): the special Frobenius pair `delta ; mu` and `id1` decide
`true` and are `CdConv`-convertible — the Bool-specific `copy;merge = id`. -/
theorem fireConvertiblePairDecidesEqual :
    decideCdConv specialFrobeniusLeftSide specialFrobeniusRightSide = true
      ∧ CdConv specialFrobeniusLeftSide specialFrobeniusRightSide :=
  ⟨rfl, RelConv.fromSpecialFrobeniusRow⟩

/-- FIRE 4 (control decides false): identity-on-two-wires versus swap have distinct Boolean matrices,
so the CD decision is `false` and they are provably NOT `CdConv`-convertible. -/
theorem fireIdentityVsSwapControlFalse :
    decideCdConv (RelDiagram.identityWires 2) RelDiagram.swapGen = false
      ∧ (CdConv (RelDiagram.identityWires 2) RelDiagram.swapGen -> False) :=
  ⟨rfl, notCdConvOfDistinctMatrices (RelDiagram.identityWires 2) RelDiagram.swapGen rfl⟩

/-- FIRE 5 (copy versus identity, at the determinism level): copy is NOT a function matrix while the
identity wire IS — the deterministic sub-PROP separates the comonoid comultiplication from a plain
wire. -/
theorem fireCopyVsIdentityDeterminismSplit :
    cdwIsDeterministic RelDiagram.copyGen = false
      ∧ cdwIsDeterministic (RelDiagram.identityWires 1) = true :=
  ⟨rfl, rfl⟩

end FX1Poly.Polygraph.Omega.Markov

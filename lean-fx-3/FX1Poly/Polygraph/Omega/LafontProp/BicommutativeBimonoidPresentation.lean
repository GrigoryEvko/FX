import FX1Poly.Polygraph.Omega.LafontProp.MatNatSemantics

/-! # Polygraph/Omega/LafontProp/BicommutativeBimonoidPresentation — the Lafont presentation of Mat(N)
(LAFONT-PROP r1, brick B: THE RELATION-DIFF GATE)

GREENFIELD LAW: fresh namespace, zero imports from the retired `WalkingBunchedBimonoid*` scope.  This
file transcribes the PUBLISHED presentation of the PROP of natural-number matrices as the free
bicommutative bimonoid, EXACTLY, with a machine-checkable relation-diff gate certifying that every
carried relation is a genuine algebraic law (a reassociation / (co)unit retraction / (co)commutativity /
bialgebra square) and NOT a disguised disjoint-strand interchange (Godement) square — the defect that
sank the previous presentation (its "unit rows" were interchange squares, so eta could never cancel into
mu, refuted r29/r30).

## THE SOURCES (the citable presentation being transcribed)

* [Lafont2003] Y. Lafont, *Towards an algebraic theory of Boolean circuits*, J. Pure Appl. Algebra 184
  (2003) 257-310.  Section 2: Theorem 1 (the symmetry tau presents the permutation category S with
  tau.tau = id and Yang-Baxter), Theorem 2 (mu, eta with associativity + two units present monotone
  maps), Theorem 3 ("The generators tau, mu, eta and the seven relations of figure 5 form a presentation
  of F" — finite sets = the PROP of commutative monoids; the right unit is DERIVABLE, figure 7).
  Section 3: the matrix semantics ("Vertical composition corresponds to the product of matrices, and
  horizontal composition to the direct sum"), the five generators tau, delta, epsilon, mu, eta with
  matrices [[0,1],[1,0]], [[1],[1]], (0x1), [[1,1]], (1x0), and Theorem 5: figure 13 = the two S
  relations (self-dual) + five F relations for (mu, eta) (covariant embedding) + five dual relations for
  (delta, epsilon) (contravariant embedding) + THE FOUR BIALGEBRA RELATIONS (verbatim):
  "delta . mu = (mu | mu) . (id1 | tau | id1) . (delta | delta),  delta . eta = eta | eta,
   epsilon . mu = epsilon | epsilon,  epsilon . eta = id0"
  + ONE EXTRA relation "mu . delta = eta . epsilon, which is specific to Z2".  The Mat(N) presentation
  is figure 13 MINUS that Z2-specific relation (see `zSpecificRelationFailsOverNat` in the kit file for
  the machine-checked failure of that row over N).  Completeness method: canonical forms + a rewrite
  system ("any diagram reduces to a canonical form", uniqueness per represented map).
* [Lack2004] S. Lack, *Composing PROPs*, Theory Appl. Categ. 13 (2004) 147-163, Section 5.3: the
  distributive law (cospans to spans by pullback) composes F^op with F; the compatibility conditions
  reduce to FOUR pullback squares ("it will suffice to consider the case q = 1 ... m and n are either 2
  or 0"), the (2,2) square being "the usual condition that delta : A -> A tensor A preserve the
  multiplication"; conclusion verbatim: "the F tensor_P F^op-algebras are precisely the commutative and
  cocommutative bialgebras", and the composite IS Mat(N): a span gives "the cardinality of each fibre of
  the map p -> m x n, which in turn is to give a function m x n -> N", i.e. free f.g. commutative-monoid
  homomorphisms N^m -> N^n (crediting [Pirashvili2002]).
* [BSZ2017] F. Bonchi, P. Sobocinski, F. Zanasi, *Interacting Hopf Algebras*, J. Pure Appl. Algebra
  221(1) (2017) 144-184 (arXiv:1403.7048), Section 2: the SMT of commutative monoids has "associativity
  (A3), commutativity (A2) and identity (A1)", the comonoid mirror is (A4)-(A6), and the bialgebra
  compatibility block (A7)-(A10) arises from "just four pullback squares (see [Lack, Section 5.3])";
  verbatim: "Therefore C ; M is the free PROP of commutative bialgebras, obtained as the quotient of
  C + M by (A7)-(A10) ... the SMT of commutative bialgebras is a presentation of the PROP Span(F)".
* [WadsleyWoods2015] S. Wadsley, N. Woods, *PROPs for linear systems* (arXiv:1505.00048): "Mat(N) is
  equivalent to the category FinSpan"; "FinSpan is the PROP for bicommutative bimonoids"; the general
  theorem: "Mat(R) is the PROP for bicommutative bimonoids A equipped with a rig map from R to the rig
  of bimonoid endomorphisms on A" (for R = N, the initial rig, the extra structure is trivial).
* [Pirashvili2002] T. Pirashvili, *On the PROP corresponding to bialgebras*, Cah. Topol. Geom. Differ.
  Categ. 43 (2002) — the alternative description of the bialgebra PROP as free f.g. commutative monoids
  (cited via [Lack2004, Section 5.3]).

## THE GENERATOR TABLE (diagram m -> n denotes an n x m matrix over N)

  | generator  | arity  | matrix          | reading            |
  |------------|--------|-----------------|--------------------|
  | mu (add)   | 2 -> 1 | [[1, 1]]        | add two wires      |
  | eta (zero) | 0 -> 1 | 1 x 0 (empty)   | constant zero      |
  | delta      | 1 -> 2 | [[1], [1]]      | copy a wire        |
  | epsilon    | 1 -> 0 | 0 x 1 (empty)   | discard a wire     |
  | tau (swap) | 2 -> 2 | [[0,1],[1,0]]   | exchange two wires |

  Sequential composition = matrix product (second stage multiplied on the left); parallel tensor =
  block-diagonal direct sum.

## THE COMPLETE RELATION CHECKLIST (every row a GENUINE law; none an interchange square)

  Core bimonoid rows (the 12 that constitute the bicommutative-bimonoid SMT; [BSZ2017] (A1)-(A10) — with
  both unit and both counit forms carried, the right forms being derivable [Lafont2003, figure 7]):
  * monoid      (M1) mu.(mu|id1) = mu.(id1|mu)         — reassociation      [BSZ (A3); Lafont fig 5]
  *             (M2) mu.(eta|id1) = id1                — LEFT-UNIT RETRACTION  [BSZ (A1); Lafont fig 5]
  *             (M3) mu.(id1|eta) = id1                — RIGHT-UNIT RETRACTION [derivable; Lafont Thm 2]
  *             (M4) mu.tau = mu                       — commutativity      [BSZ (A2); Lafont fig 5]
  * comonoid    (C1) (delta|id1).delta = (id1|delta).delta — coreassociation [BSZ (A6)]
  *             (C2) (epsilon|id1).delta = id1         — LEFT-COUNIT RETRACTION  [BSZ (A4)]
  *             (C3) (id1|epsilon).delta = id1         — RIGHT-COUNIT RETRACTION [derivable]
  *             (C4) tau.delta = delta                 — cocommutativity    [BSZ (A5)]
  * bialgebra   (B1) delta.mu = (mu|mu).(id1|tau|id1).(delta|delta) — the bialgebra square
  *             (B2) delta.eta = eta|eta
  *             (B3) epsilon.mu = epsilon|epsilon
  *             (B4) epsilon.eta = id0                 [all four: Lafont fig 13 verbatim; BSZ (A7)-(A10);
                                                        Lack Section 5.3 four pullback squares]
  Symmetry rows (PRO-style explicit symmetry, [Lafont2003] figures 5/13; in a PROP these six are part of
  the symmetric-monoidal STRUCTURE, not algebraic content — tagged separately so the diff gate can tell
  structure from content):
  * group       (S1) tau.tau = id2;  (S2) Yang-Baxter
  * naturality  (Nmu) tau.(mu|id1) = (id1|mu).(tau|id1).(id1|tau);  (Neta) tau.(eta|id1) = id1|eta;
                (Ndelta) (delta|id1).tau = (id1|tau).(tau|id1).(id1|delta);
                (Neps) (epsilon|id1).tau = id1|epsilon
  EXCLUDED: mu.delta = eta.epsilon (Z2-only, [Lafont2003] fig 13 last relation) — machine-refuted over N
  in the kit file.  EXCLUDED: any interchange/Godement row — interchange is derivable syntax-free in any
  monoidal category and carrying it as algebraic content was precisely the old defect.

## THE ANTI-GODEMENT DISCRIMINATORS (machine-checked, `relationDiffGatePasses`)

  A Godement/interchange square `(f|id).(id|g) = (id|g).(f|id)` has (i) the SAME generator multiset on
  both sides and (ii) both sides two-stage composites of tensors each containing an identity block.  The
  gate checks, per row: the (co)unit rows' right sides are the BARE identity (generator-free — impossible
  for an interchange square, whose sides both carry generators); the (co)commutativity rows' sides differ
  in swap count (1 vs 0 — impossible, interchange preserves counts); the (co)associativity rows' sides
  each END (resp. BEGIN) with the bare all-strand generator cell (impossible: a Godement stage is a
  proper tensor with an identity block, never a bare 2->1 cell consuming every strand); the bialgebra
  squares' sides differ in generator counts (1 mu + 1 delta vs 2 mu + 2 delta + 1 tau, etc. — impossible
  for interchange).  Every row is additionally SOUND: both sides denote EQUAL matrices (kernel rfl).

## COMPLETENESS ROUTE (the residual, named not proven)

  [Lafont2003] proves completeness by CANONICAL FORMS: every diagram reduces, by the relations oriented
  as rewrite rules, to a canonical representative unique per matrix (for F: permutation-stairs followed
  by monotone canonical form; for the linear case: staircase forms, Section 3.2).  [BSZ2017]/[Lack2004]
  prove it by FACTORISATION: every diagram factors as a comonoid part followed by a monoid part
  (span form n <- p -> m), unique up to permutation; equal matrices give equal spans give convertible
  diagrams.  The Lean statement is `matNatCompletenessStatement` below — the named residual of this
  brick (soundness of every row IS landed; the two defensive fires ARE landed).

Raw Lean 4 + Init.  Zero-axiom; structural recursion only; audit twin + independent witness. -/

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## The free symmetric-monoidal term syntax over the five Lafont generators -/

/-- Formal diagrams of the Lafont signature: identities, sequential composition (first stage then
second), parallel tensor (top block then bottom block), and the five generator cells.  A diagram
`sourceArity -> targetArity` denotes a `targetArity x sourceArity` matrix over N (`denoteEntries`). -/
inductive WireDiagram : Nat -> Nat -> Type where
  | identityWires : (strandCount : Nat) -> WireDiagram strandCount strandCount
  | composeSequential :
      {sourceArity : Nat} -> {middleArity : Nat} -> {targetArity : Nat} ->
      WireDiagram sourceArity middleArity -> WireDiagram middleArity targetArity ->
      WireDiagram sourceArity targetArity
  | tensorParallel :
      {topSourceArity : Nat} -> {topTargetArity : Nat} ->
      {bottomSourceArity : Nat} -> {bottomTargetArity : Nat} ->
      WireDiagram topSourceArity topTargetArity ->
      WireDiagram bottomSourceArity bottomTargetArity ->
      WireDiagram (topSourceArity + bottomSourceArity) (topTargetArity + bottomTargetArity)
  | addGen : WireDiagram 2 1
  | zeroGen : WireDiagram 0 1
  | copyGen : WireDiagram 1 2
  | discardGen : WireDiagram 1 0
  | swapGen : WireDiagram 2 2

/-- The single identity wire — the workhorse whisker block of the relation rows. -/
def singleWire : WireDiagram 1 1 := WireDiagram.identityWires 1

/-! ### Named whisker stages

Each carries a LITERAL-typed boundary so unification meets `?top + ?bottom =?= 3` (postponed, then
closed by definitional reduction) instead of decomposing `2 + 1` against `1 + 2` syntactically. -/

/-- tau | id1. -/
def swapBesideWire : WireDiagram 3 3 := WireDiagram.tensorParallel WireDiagram.swapGen singleWire

/-- id1 | tau. -/
def wireBesideSwap : WireDiagram 3 3 := WireDiagram.tensorParallel singleWire WireDiagram.swapGen

/-- mu | id1. -/
def addBesideWire : WireDiagram 3 2 := WireDiagram.tensorParallel WireDiagram.addGen singleWire

/-- id1 | mu. -/
def wireBesideAdd : WireDiagram 3 2 := WireDiagram.tensorParallel singleWire WireDiagram.addGen

/-- delta | id1. -/
def copyBesideWire : WireDiagram 2 3 := WireDiagram.tensorParallel WireDiagram.copyGen singleWire

/-- id1 | delta. -/
def wireBesideCopy : WireDiagram 2 3 := WireDiagram.tensorParallel singleWire WireDiagram.copyGen

/-- epsilon | id1. -/
def discardBesideWire : WireDiagram 2 1 :=
  WireDiagram.tensorParallel WireDiagram.discardGen singleWire

/-- id1 | epsilon. -/
def wireBesideDiscard : WireDiagram 2 1 :=
  WireDiagram.tensorParallel singleWire WireDiagram.discardGen

/-- eta | id1. -/
def zeroBesideWire : WireDiagram 1 2 := WireDiagram.tensorParallel WireDiagram.zeroGen singleWire

/-- id1 | eta. -/
def wireBesideZero : WireDiagram 1 2 := WireDiagram.tensorParallel singleWire WireDiagram.zeroGen

/-- delta | delta — the split stage of the bialgebra square. -/
def copyPairStage : WireDiagram 2 4 :=
  WireDiagram.tensorParallel WireDiagram.copyGen WireDiagram.copyGen

/-- id1 | tau | id1 (right-nested) — the middle window of the bialgebra square. -/
def innerSwapWindowStage : WireDiagram 4 4 :=
  WireDiagram.tensorParallel singleWire (WireDiagram.tensorParallel WireDiagram.swapGen singleWire)

/-- mu | mu — the merge stage of the bialgebra square. -/
def addPairStage : WireDiagram 4 2 :=
  WireDiagram.tensorParallel WireDiagram.addGen WireDiagram.addGen

/-- Matrix denotation ([Lafont2003] Section 3): identity to the identity matrix, sequential composition
to matrix product (second stage on the left), tensor to block-diagonal direct sum, generators to their
table matrices. -/
def denoteEntries : {sourceArity targetArity : Nat} -> WireDiagram sourceArity targetArity -> MatrixEntries
  | _, _, WireDiagram.identityWires _ => identityEntries
  | _, _, @WireDiagram.composeSequential _ middleArity _ firstStage secondStage =>
      composeEntries middleArity (denoteEntries secondStage) (denoteEntries firstStage)
  | _, _, @WireDiagram.tensorParallel topSourceArity topTargetArity _ _ topDiagram bottomDiagram =>
      directSumEntries topTargetArity topSourceArity (denoteEntries topDiagram) (denoteEntries bottomDiagram)
  | _, _, WireDiagram.addGen => addGenEntries
  | _, _, WireDiagram.zeroGen => zeroGenEntries
  | _, _, WireDiagram.copyGen => copyGenEntries
  | _, _, WireDiagram.discardGen => discardGenEntries
  | _, _, WireDiagram.swapGen => swapGenEntries

/-! ## Generator-use counting — the interchange-square discriminator data -/

/-- How many times each generator cell occurs in a diagram.  An interchange/Godement square has
IDENTICAL counts on both sides; the gate uses count asymmetries and generator-free sides to certify
rows are genuine laws. -/
structure GeneratorUseCounts where
  addUses : Nat
  zeroUses : Nat
  copyUses : Nat
  discardUses : Nat
  swapUses : Nat

/-- The zero count vector (identity wires). -/
def noGeneratorUses : GeneratorUseCounts :=
  { addUses := 0, zeroUses := 0, copyUses := 0, discardUses := 0, swapUses := 0 }

/-- Pointwise sum of two count vectors. -/
def addGeneratorUseCounts (leftCounts rightCounts : GeneratorUseCounts) : GeneratorUseCounts :=
  { addUses := leftCounts.addUses + rightCounts.addUses
  , zeroUses := leftCounts.zeroUses + rightCounts.zeroUses
  , copyUses := leftCounts.copyUses + rightCounts.copyUses
  , discardUses := leftCounts.discardUses + rightCounts.discardUses
  , swapUses := leftCounts.swapUses + rightCounts.swapUses }

/-- Count the generator cells occurring in a diagram. -/
def countGeneratorUses : {sourceArity targetArity : Nat} -> WireDiagram sourceArity targetArity -> GeneratorUseCounts
  | _, _, WireDiagram.identityWires _ => noGeneratorUses
  | _, _, WireDiagram.composeSequential firstStage secondStage =>
      addGeneratorUseCounts (countGeneratorUses firstStage) (countGeneratorUses secondStage)
  | _, _, WireDiagram.tensorParallel topDiagram bottomDiagram =>
      addGeneratorUseCounts (countGeneratorUses topDiagram) (countGeneratorUses bottomDiagram)
  | _, _, WireDiagram.addGen => { noGeneratorUses with addUses := 1 }
  | _, _, WireDiagram.zeroGen => { noGeneratorUses with zeroUses := 1 }
  | _, _, WireDiagram.copyGen => { noGeneratorUses with copyUses := 1 }
  | _, _, WireDiagram.discardGen => { noGeneratorUses with discardUses := 1 }
  | _, _, WireDiagram.swapGen => { noGeneratorUses with swapUses := 1 }

/-- Does the diagram have exactly the expected generator-use counts? -/
def hasGeneratorUseCounts {sourceArity targetArity : Nat} (diagram : WireDiagram sourceArity targetArity)
    (expectedAdd expectedZero expectedCopy expectedDiscard expectedSwap : Nat) : Bool :=
  let observedCounts := countGeneratorUses diagram
  Nat.beq observedCounts.addUses expectedAdd && Nat.beq observedCounts.zeroUses expectedZero
    && Nat.beq observedCounts.copyUses expectedCopy
    && Nat.beq observedCounts.discardUses expectedDiscard
    && Nat.beq observedCounts.swapUses expectedSwap

/-- Is the diagram one of the five bare generator cells? -/
def isGeneratorCell : {sourceArity targetArity : Nat} -> WireDiagram sourceArity targetArity -> Bool
  | _, _, WireDiagram.identityWires _ => false
  | _, _, WireDiagram.composeSequential _ _ => false
  | _, _, WireDiagram.tensorParallel _ _ => false
  | _, _, WireDiagram.addGen => true
  | _, _, WireDiagram.zeroGen => true
  | _, _, WireDiagram.copyGen => true
  | _, _, WireDiagram.discardGen => true
  | _, _, WireDiagram.swapGen => true

/-- Is the diagram a bare identity (generator-free by construction)?  A Godement square NEVER has a bare
identity side — this is the discriminator that convicts the old mislabeled "unit rows". -/
def isBareIdentityDiagram : {sourceArity targetArity : Nat} -> WireDiagram sourceArity targetArity -> Bool
  | _, _, WireDiagram.identityWires _ => true
  | _, _, WireDiagram.composeSequential _ _ => false
  | _, _, WireDiagram.tensorParallel _ _ => false
  | _, _, WireDiagram.addGen => false
  | _, _, WireDiagram.zeroGen => false
  | _, _, WireDiagram.copyGen => false
  | _, _, WireDiagram.discardGen => false
  | _, _, WireDiagram.swapGen => false

/-- Is the diagram a sequential composite whose SECOND stage is a bare generator cell (an all-strand
action, never a Godement stage)? -/
def isComposeEndingInGeneratorCell : {sourceArity targetArity : Nat} -> WireDiagram sourceArity targetArity -> Bool
  | _, _, WireDiagram.identityWires _ => false
  | _, _, WireDiagram.composeSequential _ secondStage => isGeneratorCell secondStage
  | _, _, WireDiagram.tensorParallel _ _ => false
  | _, _, WireDiagram.addGen => false
  | _, _, WireDiagram.zeroGen => false
  | _, _, WireDiagram.copyGen => false
  | _, _, WireDiagram.discardGen => false
  | _, _, WireDiagram.swapGen => false

/-- Is the diagram a sequential composite whose FIRST stage is a bare generator cell? -/
def isComposeStartingWithGeneratorCell : {sourceArity targetArity : Nat} -> WireDiagram sourceArity targetArity -> Bool
  | _, _, WireDiagram.identityWires _ => false
  | _, _, WireDiagram.composeSequential firstStage _ => isGeneratorCell firstStage
  | _, _, WireDiagram.tensorParallel _ _ => false
  | _, _, WireDiagram.addGen => false
  | _, _, WireDiagram.zeroGen => false
  | _, _, WireDiagram.copyGen => false
  | _, _, WireDiagram.discardGen => false
  | _, _, WireDiagram.swapGen => false

/-! ## The relation-row table -/

/-- Which family of the published presentation a row belongs to.  The symmetry families are PRO-style
STRUCTURE ([Lafont2003] carries them as relations because his ambient is a PRO; a PROP absorbs them into
the symmetric-monoidal glue); the other three families are the algebraic CONTENT — the bicommutative
bimonoid SMT of [BSZ2017] (A1)-(A10). -/
inductive LawFamilyTag : Type where
  | monoidLaw : LawFamilyTag
  | comonoidLaw : LawFamilyTag
  | bimonoidCompatibilityLaw : LawFamilyTag
  | symmetryGroupLaw : LawFamilyTag
  | symmetryNaturalityLaw : LawFamilyTag

/-- Numeric code of a law family (for `Bool` counting in the gate). -/
def lawFamilyCode : LawFamilyTag -> Nat
  | LawFamilyTag.monoidLaw => 0
  | LawFamilyTag.comonoidLaw => 1
  | LawFamilyTag.bimonoidCompatibilityLaw => 2
  | LawFamilyTag.symmetryGroupLaw => 3
  | LawFamilyTag.symmetryNaturalityLaw => 4

/-- One relation of the presentation: two diagrams of matching arities plus the family tag. -/
structure RelationRow where
  sourceArity : Nat
  targetArity : Nat
  leftSide : WireDiagram sourceArity targetArity
  rightSide : WireDiagram sourceArity targetArity
  familyTag : LawFamilyTag

/-- SOUNDNESS of one row: both sides denote the SAME matrix on the full rectangle. -/
def isRowSoundOverMatrices (row : RelationRow) : Bool :=
  doEntriesAgreeUpTo row.targetArity row.sourceArity
    (denoteEntries row.leftSide) (denoteEntries row.rightSide)

/-! ### Monoid rows ([BSZ2017] (A1)-(A3) + derivable right unit; [Lafont2003] figure 5) -/

/-- (M1) left side: (mu | id1) ; mu — reassociation, NOT an interchange square (both stages overlap on
the middle strand; the second stage is the bare all-strand mu). -/
def addAssociativityLeftSide : WireDiagram 3 1 :=
  WireDiagram.composeSequential addBesideWire WireDiagram.addGen

/-- (M1) right side: (id1 | mu) ; mu. -/
def addAssociativityRightSide : WireDiagram 3 1 :=
  WireDiagram.composeSequential wireBesideAdd WireDiagram.addGen

/-- (M1) mu associativity — [BSZ2017] (A3), [Lafont2003] figure 5. -/
def addAssociativityRow : RelationRow :=
  { sourceArity := 3, targetArity := 1
  , leftSide := addAssociativityLeftSide, rightSide := addAssociativityRightSide
  , familyTag := LawFamilyTag.monoidLaw }

/-- (M2) left side: (eta | id1) ; mu. -/
def addLeftUnitLeftSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential zeroBesideWire WireDiagram.addGen

/-- (M2) right side: the BARE identity — the retraction shape no interchange square can have. -/
def addLeftUnitRightSide : WireDiagram 1 1 := WireDiagram.identityWires 1

/-- (M2) mu left unit — [BSZ2017] (A1), [Lafont2003] figure 5.  THE law whose absence sank the old
presentation. -/
def addLeftUnitRow : RelationRow :=
  { sourceArity := 1, targetArity := 1
  , leftSide := addLeftUnitLeftSide, rightSide := addLeftUnitRightSide
  , familyTag := LawFamilyTag.monoidLaw }

/-- (M3) left side: (id1 | eta) ; mu. -/
def addRightUnitLeftSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential wireBesideZero WireDiagram.addGen

/-- (M3) right side: the bare identity. -/
def addRightUnitRightSide : WireDiagram 1 1 := WireDiagram.identityWires 1

/-- (M3) mu right unit — derivable from (M2)+(M4)+naturality ([Lafont2003] Theorem 2 lists it, figure 7
derives it in F); carried explicitly so the unit pair fires one-step. -/
def addRightUnitRow : RelationRow :=
  { sourceArity := 1, targetArity := 1
  , leftSide := addRightUnitLeftSide, rightSide := addRightUnitRightSide
  , familyTag := LawFamilyTag.monoidLaw }

/-- (M4) left side: tau ; mu. -/
def addCommutativityLeftSide : WireDiagram 2 1 :=
  WireDiagram.composeSequential WireDiagram.swapGen WireDiagram.addGen

/-- (M4) right side: bare mu — one swap fewer than the left side (interchange-impossible asymmetry). -/
def addCommutativityRightSide : WireDiagram 2 1 := WireDiagram.addGen

/-- (M4) mu commutativity — [BSZ2017] (A2), [Lafont2003] figure 5 ("mu . tau = mu"). -/
def addCommutativityRow : RelationRow :=
  { sourceArity := 2, targetArity := 1
  , leftSide := addCommutativityLeftSide, rightSide := addCommutativityRightSide
  , familyTag := LawFamilyTag.monoidLaw }

/-! ### Comonoid rows ([BSZ2017] (A4)-(A6) + derivable right counit; [Lafont2003] figure 13 duals) -/

/-- (C1) left side: delta ; (delta | id1). -/
def copyCoassociativityLeftSide : WireDiagram 1 3 :=
  WireDiagram.composeSequential WireDiagram.copyGen copyBesideWire

/-- (C1) right side: delta ; (id1 | delta). -/
def copyCoassociativityRightSide : WireDiagram 1 3 :=
  WireDiagram.composeSequential WireDiagram.copyGen wireBesideCopy

/-- (C1) delta coassociativity — [BSZ2017] (A6), the transpose of (M1). -/
def copyCoassociativityRow : RelationRow :=
  { sourceArity := 1, targetArity := 3
  , leftSide := copyCoassociativityLeftSide, rightSide := copyCoassociativityRightSide
  , familyTag := LawFamilyTag.comonoidLaw }

/-- (C2) left side: delta ; (epsilon | id1). -/
def copyLeftCounitLeftSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential WireDiagram.copyGen discardBesideWire

/-- (C2) right side: the bare identity. -/
def copyLeftCounitRightSide : WireDiagram 1 1 := WireDiagram.identityWires 1

/-- (C2) delta left counit — [BSZ2017] (A4), the transpose of (M2). -/
def copyLeftCounitRow : RelationRow :=
  { sourceArity := 1, targetArity := 1
  , leftSide := copyLeftCounitLeftSide, rightSide := copyLeftCounitRightSide
  , familyTag := LawFamilyTag.comonoidLaw }

/-- (C3) left side: delta ; (id1 | epsilon). -/
def copyRightCounitLeftSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential WireDiagram.copyGen wireBesideDiscard

/-- (C3) right side: the bare identity. -/
def copyRightCounitRightSide : WireDiagram 1 1 := WireDiagram.identityWires 1

/-- (C3) delta right counit — derivable dual of (M3); carried explicitly. -/
def copyRightCounitRow : RelationRow :=
  { sourceArity := 1, targetArity := 1
  , leftSide := copyRightCounitLeftSide, rightSide := copyRightCounitRightSide
  , familyTag := LawFamilyTag.comonoidLaw }

/-- (C4) left side: delta ; tau. -/
def copyCocommutativityLeftSide : WireDiagram 1 2 :=
  WireDiagram.composeSequential WireDiagram.copyGen WireDiagram.swapGen

/-- (C4) right side: bare delta. -/
def copyCocommutativityRightSide : WireDiagram 1 2 := WireDiagram.copyGen

/-- (C4) delta cocommutativity — [BSZ2017] (A5), the transpose of (M4). -/
def copyCocommutativityRow : RelationRow :=
  { sourceArity := 1, targetArity := 2
  , leftSide := copyCocommutativityLeftSide, rightSide := copyCocommutativityRightSide
  , familyTag := LawFamilyTag.comonoidLaw }

/-! ### The four bialgebra squares ([Lafont2003] figure 13 verbatim; [BSZ2017] (A7)-(A10);
[Lack2004] Section 5.3 four pullback squares) -/

/-- (B1) left side: mu ; delta. -/
def copyAfterAddLeftSide : WireDiagram 2 2 :=
  WireDiagram.composeSequential WireDiagram.addGen WireDiagram.copyGen

/-- (B1) right side: (delta | delta) ; (id1 | tau | id1) ; (mu | mu) — the middle tensor right-nested. -/
def copyAfterAddRightSide : WireDiagram 2 2 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential copyPairStage innerSwapWindowStage) addPairStage

/-- (B1) the bialgebra square "delta . mu = (mu | mu) . (id1 | tau | id1) . (delta | delta)"
([Lafont2003] figure 13; [Lack2004]: "the usual condition that delta preserve the multiplication").
Both sides denote the all-ones 2x2 matrix. -/
def copyAfterAddBimonoidRow : RelationRow :=
  { sourceArity := 2, targetArity := 2
  , leftSide := copyAfterAddLeftSide, rightSide := copyAfterAddRightSide
  , familyTag := LawFamilyTag.bimonoidCompatibilityLaw }

/-- (B2) left side: eta ; delta. -/
def copyAfterZeroLeftSide : WireDiagram 0 2 :=
  WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen

/-- (B2) right side: eta | eta. -/
def copyAfterZeroRightSide : WireDiagram 0 2 :=
  WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen

/-- (B2) "delta . eta = eta | eta" ([Lafont2003] figure 13 verbatim). -/
def copyAfterZeroBimonoidRow : RelationRow :=
  { sourceArity := 0, targetArity := 2
  , leftSide := copyAfterZeroLeftSide, rightSide := copyAfterZeroRightSide
  , familyTag := LawFamilyTag.bimonoidCompatibilityLaw }

/-- (B3) left side: mu ; epsilon. -/
def discardAfterAddLeftSide : WireDiagram 2 0 :=
  WireDiagram.composeSequential WireDiagram.addGen WireDiagram.discardGen

/-- (B3) right side: epsilon | epsilon. -/
def discardAfterAddRightSide : WireDiagram 2 0 :=
  WireDiagram.tensorParallel WireDiagram.discardGen WireDiagram.discardGen

/-- (B3) "epsilon . mu = epsilon | epsilon" ([Lafont2003] figure 13 verbatim). -/
def discardAfterAddBimonoidRow : RelationRow :=
  { sourceArity := 2, targetArity := 0
  , leftSide := discardAfterAddLeftSide, rightSide := discardAfterAddRightSide
  , familyTag := LawFamilyTag.bimonoidCompatibilityLaw }

/-- (B4) left side: eta ; epsilon. -/
def discardAfterZeroLeftSide : WireDiagram 0 0 :=
  WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen

/-- (B4) right side: the bare empty identity id0. -/
def discardAfterZeroRightSide : WireDiagram 0 0 := WireDiagram.identityWires 0

/-- (B4) "epsilon . eta = id0" ([Lafont2003] figure 13 verbatim). -/
def discardAfterZeroBimonoidRow : RelationRow :=
  { sourceArity := 0, targetArity := 0
  , leftSide := discardAfterZeroLeftSide, rightSide := discardAfterZeroRightSide
  , familyTag := LawFamilyTag.bimonoidCompatibilityLaw }

/-! ### Symmetry rows (PRO-style structure, [Lafont2003] figures 5/13; PROP glue, not content) -/

/-- (S1) left side: tau ; tau. -/
def swapInvolutionLeftSide : WireDiagram 2 2 :=
  WireDiagram.composeSequential WireDiagram.swapGen WireDiagram.swapGen

/-- (S1) right side: id2. -/
def swapInvolutionRightSide : WireDiagram 2 2 := WireDiagram.identityWires 2

/-- (S1) "tau . tau = id2" ([Lafont2003] Theorem 1). -/
def swapInvolutionRow : RelationRow :=
  { sourceArity := 2, targetArity := 2
  , leftSide := swapInvolutionLeftSide, rightSide := swapInvolutionRightSide
  , familyTag := LawFamilyTag.symmetryGroupLaw }

/-- (S2) left side: (tau | id1) ; (id1 | tau) ; (tau | id1). -/
def swapYangBaxterLeftSide : WireDiagram 3 3 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential swapBesideWire wireBesideSwap) swapBesideWire

/-- (S2) right side: (id1 | tau) ; (tau | id1) ; (id1 | tau). -/
def swapYangBaxterRightSide : WireDiagram 3 3 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential wireBesideSwap swapBesideWire) wireBesideSwap

/-- (S2) the Yang-Baxter braid relation ([Lafont2003] Theorem 1). -/
def swapYangBaxterRow : RelationRow :=
  { sourceArity := 3, targetArity := 3
  , leftSide := swapYangBaxterLeftSide, rightSide := swapYangBaxterRightSide
  , familyTag := LawFamilyTag.symmetryGroupLaw }

/-- (Nmu) left side: (mu | id1) ; tau. -/
def swapPastAddLeftSide : WireDiagram 3 2 :=
  WireDiagram.composeSequential addBesideWire WireDiagram.swapGen

/-- (Nmu) right side: (id1 | tau) ; (tau | id1) ; (id1 | mu). -/
def swapPastAddRightSide : WireDiagram 3 2 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential wireBesideSwap swapBesideWire) wireBesideAdd

/-- (Nmu) naturality of tau at mu: "tau . (mu | id1) = (id1 | mu) . (tau | id1) . (id1 | tau)"
([Lafont2003] figure 5 verbatim). -/
def swapPastAddNaturalityRow : RelationRow :=
  { sourceArity := 3, targetArity := 2
  , leftSide := swapPastAddLeftSide, rightSide := swapPastAddRightSide
  , familyTag := LawFamilyTag.symmetryNaturalityLaw }

/-- (Neta) left side: (eta | id1) ; tau. -/
def swapPastZeroLeftSide : WireDiagram 1 2 :=
  WireDiagram.composeSequential zeroBesideWire WireDiagram.swapGen

/-- (Neta) right side: id1 | eta. -/
def swapPastZeroRightSide : WireDiagram 1 2 := wireBesideZero

/-- (Neta) naturality of tau at eta: "tau . (eta | id1) = id1 | eta" ([Lafont2003] figure 5 verbatim). -/
def swapPastZeroNaturalityRow : RelationRow :=
  { sourceArity := 1, targetArity := 2
  , leftSide := swapPastZeroLeftSide, rightSide := swapPastZeroRightSide
  , familyTag := LawFamilyTag.symmetryNaturalityLaw }

/-- (Ndelta) left side: tau ; (delta | id1). -/
def copyPastSwapLeftSide : WireDiagram 2 3 :=
  WireDiagram.composeSequential WireDiagram.swapGen copyBesideWire

/-- (Ndelta) right side: (id1 | delta) ; (tau | id1) ; (id1 | tau). -/
def copyPastSwapRightSide : WireDiagram 2 3 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential wireBesideCopy swapBesideWire) wireBesideSwap

/-- (Ndelta) naturality of tau at delta: "(delta | id1) . tau = (id1 | tau) . (tau | id1) . (id1 | delta)"
(the transpose of (Nmu); [Lafont2003] figure 13 dual block). -/
def copyPastSwapNaturalityRow : RelationRow :=
  { sourceArity := 2, targetArity := 3
  , leftSide := copyPastSwapLeftSide, rightSide := copyPastSwapRightSide
  , familyTag := LawFamilyTag.symmetryNaturalityLaw }

/-- (Neps) left side: tau ; (epsilon | id1). -/
def discardPastSwapLeftSide : WireDiagram 2 1 :=
  WireDiagram.composeSequential WireDiagram.swapGen discardBesideWire

/-- (Neps) right side: id1 | epsilon. -/
def discardPastSwapRightSide : WireDiagram 2 1 := wireBesideDiscard

/-- (Neps) naturality of tau at epsilon: "(epsilon | id1) . tau = id1 | epsilon" (the transpose of
(Neta); [Lafont2003] figure 13 dual block). -/
def discardPastSwapNaturalityRow : RelationRow :=
  { sourceArity := 2, targetArity := 1
  , leftSide := discardPastSwapLeftSide, rightSide := discardPastSwapRightSide
  , familyTag := LawFamilyTag.symmetryNaturalityLaw }

/-- THE FULL TABLE: 12 core bimonoid rows + 2 symmetry-group rows + 4 symmetry-naturality rows =
[Lafont2003] figure 13 MINUS the Z2-specific row, PLUS the two derivable right-(co)unit forms. -/
def lafontRelationRows : List RelationRow :=
  [ addAssociativityRow, addLeftUnitRow, addRightUnitRow, addCommutativityRow
  , copyCoassociativityRow, copyLeftCounitRow, copyRightCounitRow, copyCocommutativityRow
  , copyAfterAddBimonoidRow, copyAfterZeroBimonoidRow, discardAfterAddBimonoidRow
  , discardAfterZeroBimonoidRow
  , swapInvolutionRow, swapYangBaxterRow
  , swapPastAddNaturalityRow, swapPastZeroNaturalityRow, copyPastSwapNaturalityRow
  , discardPastSwapNaturalityRow ]

/-! ## Per-row soundness (kernel rfl): every relation maps to EQUAL matrices -/

theorem addAssociativityRow_isSoundOverMatrices : isRowSoundOverMatrices addAssociativityRow = true := rfl
theorem addLeftUnitRow_isSoundOverMatrices : isRowSoundOverMatrices addLeftUnitRow = true := rfl
theorem addRightUnitRow_isSoundOverMatrices : isRowSoundOverMatrices addRightUnitRow = true := rfl
theorem addCommutativityRow_isSoundOverMatrices : isRowSoundOverMatrices addCommutativityRow = true := rfl
theorem copyCoassociativityRow_isSoundOverMatrices : isRowSoundOverMatrices copyCoassociativityRow = true := rfl
theorem copyLeftCounitRow_isSoundOverMatrices : isRowSoundOverMatrices copyLeftCounitRow = true := rfl
theorem copyRightCounitRow_isSoundOverMatrices : isRowSoundOverMatrices copyRightCounitRow = true := rfl
theorem copyCocommutativityRow_isSoundOverMatrices : isRowSoundOverMatrices copyCocommutativityRow = true := rfl
theorem copyAfterAddBimonoidRow_isSoundOverMatrices : isRowSoundOverMatrices copyAfterAddBimonoidRow = true := rfl
theorem copyAfterZeroBimonoidRow_isSoundOverMatrices : isRowSoundOverMatrices copyAfterZeroBimonoidRow = true := rfl
theorem discardAfterAddBimonoidRow_isSoundOverMatrices : isRowSoundOverMatrices discardAfterAddBimonoidRow = true := rfl
theorem discardAfterZeroBimonoidRow_isSoundOverMatrices : isRowSoundOverMatrices discardAfterZeroBimonoidRow = true := rfl
theorem swapInvolutionRow_isSoundOverMatrices : isRowSoundOverMatrices swapInvolutionRow = true := rfl
theorem swapYangBaxterRow_isSoundOverMatrices : isRowSoundOverMatrices swapYangBaxterRow = true := rfl
theorem swapPastAddNaturalityRow_isSoundOverMatrices : isRowSoundOverMatrices swapPastAddNaturalityRow = true := rfl
theorem swapPastZeroNaturalityRow_isSoundOverMatrices : isRowSoundOverMatrices swapPastZeroNaturalityRow = true := rfl
theorem copyPastSwapNaturalityRow_isSoundOverMatrices : isRowSoundOverMatrices copyPastSwapNaturalityRow = true := rfl
theorem discardPastSwapNaturalityRow_isSoundOverMatrices : isRowSoundOverMatrices discardPastSwapNaturalityRow = true := rfl

/-! ## THE RELATION-DIFF GATE — the machine-checkable checklist decl -/

/-- Fold: are all rows of a table sound over matrices?  (Monomorphic — no polymorphic list lemmas.) -/
def areAllRowsSoundIn : List RelationRow -> Bool
  | [] => true
  | headRow :: tailRows => isRowSoundOverMatrices headRow && areAllRowsSoundIn tailRows

/-- Count the rows carrying a given family code. -/
def countRowsWithFamilyCode (familyCode : Nat) : List RelationRow -> Nat
  | [] => 0
  | headRow :: tailRows =>
      cond (Nat.beq (lawFamilyCode headRow.familyTag) familyCode) 1 0
        + countRowsWithFamilyCode familyCode tailRows

/-- GATE CHECK 1: every row of the table is sound (equal matrices both sides). -/
def areAllRelationRowsSoundOverMatrices : Bool := areAllRowsSoundIn lafontRelationRows

/-- GATE CHECK 2: the row inventory matches the published presentation — 18 rows total: 4 monoid +
4 comonoid + 4 bialgebra (the 12-row bicommutative-bimonoid SMT with derivable right forms carried) +
2 symmetry-group + 4 symmetry-naturality ([Lafont2003] figure 13 minus the Z2-specific row, plus the two
derivable right forms). -/
def doesRowInventoryMatchLafont : Bool :=
  Nat.beq lafontRelationRows.length 18
    && Nat.beq (countRowsWithFamilyCode 0 lafontRelationRows) 4
    && Nat.beq (countRowsWithFamilyCode 1 lafontRelationRows) 4
    && Nat.beq (countRowsWithFamilyCode 2 lafontRelationRows) 4
    && Nat.beq (countRowsWithFamilyCode 3 lafontRelationRows) 2
    && Nat.beq (countRowsWithFamilyCode 4 lafontRelationRows) 4

/-- GATE CHECK 3: the five retraction rows ((co)units and epsilon.eta) have a BARE-IDENTITY right side
and the exact one-generator-each left side — the shape NO interchange/Godement square can have (both
Godement sides carry the same nonempty generator multiset).  This is the check whose absence let the old
presentation ship interchange squares as "unit laws". -/
def areUnitRowsGenuineRetractions : Bool :=
  isBareIdentityDiagram addLeftUnitRow.rightSide
    && hasGeneratorUseCounts addLeftUnitRow.leftSide 1 1 0 0 0
    && isBareIdentityDiagram addRightUnitRow.rightSide
    && hasGeneratorUseCounts addRightUnitRow.leftSide 1 1 0 0 0
    && isBareIdentityDiagram copyLeftCounitRow.rightSide
    && hasGeneratorUseCounts copyLeftCounitRow.leftSide 0 0 1 1 0
    && isBareIdentityDiagram copyRightCounitRow.rightSide
    && hasGeneratorUseCounts copyRightCounitRow.leftSide 0 0 1 1 0
    && isBareIdentityDiagram discardAfterZeroBimonoidRow.rightSide
    && hasGeneratorUseCounts discardAfterZeroBimonoidRow.leftSide 0 1 0 1 0

/-- GATE CHECK 4: the (co)commutativity rows are swap-ASYMMETRIC (one side has a tau, the other does
not) — interchange squares preserve generator counts, so neither row can be one. -/
def areCommutativityRowsSwapAsymmetric : Bool :=
  hasGeneratorUseCounts addCommutativityRow.leftSide 1 0 0 0 1
    && hasGeneratorUseCounts addCommutativityRow.rightSide 1 0 0 0 0
    && hasGeneratorUseCounts copyCocommutativityRow.leftSide 0 0 1 0 1
    && hasGeneratorUseCounts copyCocommutativityRow.rightSide 0 0 1 0 0

/-- GATE CHECK 5: the (co)associativity rows have both sides ENDING (resp. STARTING) in the bare
all-strand generator cell, with exactly two occurrences of it and no swap — a Godement square's stages
are proper tensors with identity blocks acting on DISJOINT strands, never a bare 2->1 (1->2) cell
consuming (producing) every strand, so neither row can be a transported interchange. -/
def areAssociativityRowsTotalOverlap : Bool :=
  isComposeEndingInGeneratorCell addAssociativityRow.leftSide
    && isComposeEndingInGeneratorCell addAssociativityRow.rightSide
    && hasGeneratorUseCounts addAssociativityRow.leftSide 2 0 0 0 0
    && hasGeneratorUseCounts addAssociativityRow.rightSide 2 0 0 0 0
    && isComposeStartingWithGeneratorCell copyCoassociativityRow.leftSide
    && isComposeStartingWithGeneratorCell copyCoassociativityRow.rightSide
    && hasGeneratorUseCounts copyCoassociativityRow.leftSide 0 0 2 0 0
    && hasGeneratorUseCounts copyCoassociativityRow.rightSide 0 0 2 0 0

/-- GATE CHECK 6: the three nontrivial bialgebra squares carry the exact published generator counts —
count-ASYMMETRIC between sides (1 mu + 1 delta vs 2 mu + 2 delta + 1 tau, etc.), so none is an
interchange square. -/
def areBimonoidSquaresLafontExact : Bool :=
  hasGeneratorUseCounts copyAfterAddBimonoidRow.leftSide 1 0 1 0 0
    && hasGeneratorUseCounts copyAfterAddBimonoidRow.rightSide 2 0 2 0 1
    && hasGeneratorUseCounts copyAfterZeroBimonoidRow.leftSide 0 1 1 0 0
    && hasGeneratorUseCounts copyAfterZeroBimonoidRow.rightSide 0 2 0 0 0
    && hasGeneratorUseCounts discardAfterAddBimonoidRow.leftSide 1 0 0 1 0
    && hasGeneratorUseCounts discardAfterAddBimonoidRow.rightSide 0 0 0 2 0

/-- THE RELATION-DIFF GATE: all six checks at once.  `relationDiffGatePasses` is the machine-checkable
checklist decl demanded before any proving: the presentation carries EACH published relation as a genuine
law row, sound over Mat(N), with the anti-Godement discriminators all firing. -/
def doesRelationDiffGatePass : Bool :=
  areAllRelationRowsSoundOverMatrices && doesRowInventoryMatchLafont
    && areUnitRowsGenuineRetractions && areCommutativityRowsSwapAsymmetric
    && areAssociativityRowsTotalOverlap && areBimonoidSquaresLafontExact

/-- THE GATE FIRES (kernel rfl). -/
theorem relationDiffGatePasses : doesRelationDiffGatePass = true := rfl

/-- Syntactic pin: the five retraction rows' right sides are the bare identity ON THE NOSE (definitional
equality, not just the Bool checker) — the strongest form of the anti-Godement certificate. -/
theorem unitRowRightSidesAreBareIdentity :
    addLeftUnitRow.rightSide = WireDiagram.identityWires 1
      ∧ addRightUnitRow.rightSide = WireDiagram.identityWires 1
      ∧ copyLeftCounitRow.rightSide = WireDiagram.identityWires 1
      ∧ copyRightCounitRow.rightSide = WireDiagram.identityWires 1
      ∧ discardAfterZeroBimonoidRow.rightSide = WireDiagram.identityWires 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Convertibility — the presented congruence -/

/-- The smallest congruence on diagrams containing the 18 relation rows and the strict-monoidal
structural laws (identities, reassociation of sequential composition, identity-tensor fusion, and the
middle-four interchange — the interchange lives HERE, as structural glue, never as a relation row).
Symmetry naturality at compound diagrams and tensor reassociation across nonassociated Nat indices are
generated from the row/structural constructors on concrete instances. -/
inductive AreConvertibleDiagrams :
    {sourceArity : Nat} -> {targetArity : Nat} ->
    WireDiagram sourceArity targetArity -> WireDiagram sourceArity targetArity -> Prop where
  | fromReflexivity {sourceArity targetArity : Nat}
      (diagram : WireDiagram sourceArity targetArity) :
      AreConvertibleDiagrams diagram diagram
  | fromSymmetry {sourceArity targetArity : Nat}
      {leftDiagram rightDiagram : WireDiagram sourceArity targetArity} :
      AreConvertibleDiagrams leftDiagram rightDiagram ->
      AreConvertibleDiagrams rightDiagram leftDiagram
  | fromTransitivity {sourceArity targetArity : Nat}
      {leftDiagram middleDiagram rightDiagram : WireDiagram sourceArity targetArity} :
      AreConvertibleDiagrams leftDiagram middleDiagram ->
      AreConvertibleDiagrams middleDiagram rightDiagram ->
      AreConvertibleDiagrams leftDiagram rightDiagram
  | underComposeSequential {sourceArity middleArity targetArity : Nat}
      {firstLeft firstRight : WireDiagram sourceArity middleArity}
      {secondLeft secondRight : WireDiagram middleArity targetArity} :
      AreConvertibleDiagrams firstLeft firstRight ->
      AreConvertibleDiagrams secondLeft secondRight ->
      AreConvertibleDiagrams (WireDiagram.composeSequential firstLeft secondLeft)
        (WireDiagram.composeSequential firstRight secondRight)
  | underTensorParallel {topSourceArity topTargetArity bottomSourceArity bottomTargetArity : Nat}
      {topLeft topRight : WireDiagram topSourceArity topTargetArity}
      {bottomLeft bottomRight : WireDiagram bottomSourceArity bottomTargetArity} :
      AreConvertibleDiagrams topLeft topRight ->
      AreConvertibleDiagrams bottomLeft bottomRight ->
      AreConvertibleDiagrams (WireDiagram.tensorParallel topLeft bottomLeft)
        (WireDiagram.tensorParallel topRight bottomRight)
  | composeIdentitySource {sourceArity targetArity : Nat}
      (diagram : WireDiagram sourceArity targetArity) :
      AreConvertibleDiagrams
        (WireDiagram.composeSequential (WireDiagram.identityWires sourceArity) diagram) diagram
  | composeIdentityTarget {sourceArity targetArity : Nat}
      (diagram : WireDiagram sourceArity targetArity) :
      AreConvertibleDiagrams
        (WireDiagram.composeSequential diagram (WireDiagram.identityWires targetArity)) diagram
  | composeReassociate {sourceArity secondArity thirdArity targetArity : Nat}
      (firstStage : WireDiagram sourceArity secondArity)
      (secondStage : WireDiagram secondArity thirdArity)
      (thirdStage : WireDiagram thirdArity targetArity) :
      AreConvertibleDiagrams
        (WireDiagram.composeSequential (WireDiagram.composeSequential firstStage secondStage) thirdStage)
        (WireDiagram.composeSequential firstStage (WireDiagram.composeSequential secondStage thirdStage))
  | tensorIdentityFusion (topStrandCount bottomStrandCount : Nat) :
      AreConvertibleDiagrams
        (WireDiagram.tensorParallel (WireDiagram.identityWires topStrandCount)
          (WireDiagram.identityWires bottomStrandCount))
        (WireDiagram.identityWires (topStrandCount + bottomStrandCount))
  | middleFourInterchange {topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity : Nat}
      (topFirst : WireDiagram topSourceArity topMiddleArity)
      (topSecond : WireDiagram topMiddleArity topTargetArity)
      (bottomFirst : WireDiagram bottomSourceArity bottomMiddleArity)
      (bottomSecond : WireDiagram bottomMiddleArity bottomTargetArity) :
      AreConvertibleDiagrams
        (WireDiagram.tensorParallel (WireDiagram.composeSequential topFirst topSecond)
          (WireDiagram.composeSequential bottomFirst bottomSecond))
        (WireDiagram.composeSequential (WireDiagram.tensorParallel topFirst bottomFirst)
          (WireDiagram.tensorParallel topSecond bottomSecond))
  | fromAddAssociativityRow :
      AreConvertibleDiagrams addAssociativityLeftSide addAssociativityRightSide
  | fromAddLeftUnitRow : AreConvertibleDiagrams addLeftUnitLeftSide addLeftUnitRightSide
  | fromAddRightUnitRow : AreConvertibleDiagrams addRightUnitLeftSide addRightUnitRightSide
  | fromAddCommutativityRow :
      AreConvertibleDiagrams addCommutativityLeftSide addCommutativityRightSide
  | fromCopyCoassociativityRow :
      AreConvertibleDiagrams copyCoassociativityLeftSide copyCoassociativityRightSide
  | fromCopyLeftCounitRow : AreConvertibleDiagrams copyLeftCounitLeftSide copyLeftCounitRightSide
  | fromCopyRightCounitRow : AreConvertibleDiagrams copyRightCounitLeftSide copyRightCounitRightSide
  | fromCopyCocommutativityRow :
      AreConvertibleDiagrams copyCocommutativityLeftSide copyCocommutativityRightSide
  | fromCopyAfterAddBimonoidRow :
      AreConvertibleDiagrams copyAfterAddLeftSide copyAfterAddRightSide
  | fromCopyAfterZeroBimonoidRow :
      AreConvertibleDiagrams copyAfterZeroLeftSide copyAfterZeroRightSide
  | fromDiscardAfterAddBimonoidRow :
      AreConvertibleDiagrams discardAfterAddLeftSide discardAfterAddRightSide
  | fromDiscardAfterZeroBimonoidRow :
      AreConvertibleDiagrams discardAfterZeroLeftSide discardAfterZeroRightSide
  | fromSwapInvolutionRow : AreConvertibleDiagrams swapInvolutionLeftSide swapInvolutionRightSide
  | fromSwapYangBaxterRow : AreConvertibleDiagrams swapYangBaxterLeftSide swapYangBaxterRightSide
  | fromSwapPastAddNaturalityRow :
      AreConvertibleDiagrams swapPastAddLeftSide swapPastAddRightSide
  | fromSwapPastZeroNaturalityRow :
      AreConvertibleDiagrams swapPastZeroLeftSide swapPastZeroRightSide
  | fromCopyPastSwapNaturalityRow :
      AreConvertibleDiagrams copyPastSwapLeftSide copyPastSwapRightSide
  | fromDiscardPastSwapNaturalityRow :
      AreConvertibleDiagrams discardPastSwapLeftSide discardPastSwapRightSide

/-! ## THE DEFENSIVE FIRES — the exact pairs that refuted the old star, now convertible

The r30 refutation pair: "(a <| eta_a) ; mu_a vs id_a passes ALL premises ... yet separates" — in this
presentation it is the right-unit ROW and fires one-step.  The associativity pair
"(mu whisker a) ; mu vs (a whisker mu) ; mu" is the associativity ROW.  Were either NOT convertible
here, the relation set would still be incomplete — they are, by construction, single row firings. -/

/-- THE REFUTED UNIT PAIR, left side: (id1 | eta) ; mu — eta whiskered by the single strand, then mu. -/
def refutedUnitPairLeftSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential wireBesideZero WireDiagram.addGen

/-- The refuted unit pair IS the right-unit row (syntactic identity). -/
theorem refutedUnitPairMatchesAddRightUnitRow : refutedUnitPairLeftSide = addRightUnitLeftSide := rfl

/-- DEFENSIVE FIRE 1: the pair that refuted the old star is CONVERTIBLE here — one row firing. -/
theorem refutedUnitPairIsNowConvertible :
    AreConvertibleDiagrams refutedUnitPairLeftSide (WireDiagram.identityWires 1) :=
  AreConvertibleDiagrams.fromAddRightUnitRow

/-- The unit pair's two sides denote the SAME 1x1 matrix [[1]] (the old star's premise, kernel rfl). -/
theorem refutedUnitPairHasEqualMatrices :
    doEntriesAgreeUpTo 1 1 (denoteEntries refutedUnitPairLeftSide)
      (denoteEntries (WireDiagram.identityWires 1)) = true := rfl

/-- The mirror unit pair (eta | id1) ; mu — also convertible, via the left-unit row. -/
theorem mirrorUnitPairIsNowConvertible :
    AreConvertibleDiagrams addLeftUnitLeftSide (WireDiagram.identityWires 1) :=
  AreConvertibleDiagrams.fromAddLeftUnitRow

/-- THE REFUTED ASSOCIATIVITY PAIR, left side: (mu | id1) ; mu — mu whiskered right by the strand. -/
def refutedAssociativityPairLeftSide : WireDiagram 3 1 :=
  WireDiagram.composeSequential addBesideWire WireDiagram.addGen

/-- THE REFUTED ASSOCIATIVITY PAIR, right side: (id1 | mu) ; mu. -/
def refutedAssociativityPairRightSide : WireDiagram 3 1 :=
  WireDiagram.composeSequential wireBesideAdd WireDiagram.addGen

/-- The associativity pair IS the associativity row (syntactic identity, both sides). -/
theorem refutedAssociativityPairMatchesRow :
    refutedAssociativityPairLeftSide = addAssociativityLeftSide
      ∧ refutedAssociativityPairRightSide = addAssociativityRightSide := ⟨rfl, rfl⟩

/-- DEFENSIVE FIRE 2: the associativity pair is CONVERTIBLE here — one row firing. -/
theorem refutedAssociativityPairIsNowConvertible :
    AreConvertibleDiagrams refutedAssociativityPairLeftSide refutedAssociativityPairRightSide :=
  AreConvertibleDiagrams.fromAddAssociativityRow

/-- The associativity pair's sides denote the same 1x3 matrix [[1,1,1]] (kernel rfl). -/
theorem refutedAssociativityPairHasEqualMatrices :
    doEntriesAgreeUpTo 1 3 (denoteEntries refutedAssociativityPairLeftSide)
      (denoteEntries refutedAssociativityPairRightSide) = true := rfl

/-- A DERIVED (multi-step) fire exercising the congruence machinery: eta ; ((eta | id1) ; mu) converts
to eta — congruence under composition with the left-unit row, then the identity-target structural law,
chained by transitivity. -/
def derivedZeroThenLeftUnitChain : WireDiagram 0 1 :=
  WireDiagram.composeSequential WireDiagram.zeroGen addLeftUnitLeftSide

/-- DEFENSIVE FIRE 3 (derived): the three-step conversion eta ; ((eta | id1) ; mu) ~> eta. -/
theorem derivedZeroThenLeftUnitChainConverts :
    AreConvertibleDiagrams derivedZeroThenLeftUnitChain WireDiagram.zeroGen :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromAddLeftUnitRow)
    (AreConvertibleDiagrams.composeIdentityTarget WireDiagram.zeroGen)

/-! ## Named residuals (owner false — stated, NOT proven here) -/

/-- RESIDUAL 1 (congruence soundness): every convertible pair denotes equal matrices.  Each ROW is
already sound by kernel rfl (the 18 `_isSoundOverMatrices` theorems); the congruence-closure lift needs
the rectangle-agreement algebra for product/direct-sum under agreement, sum-exchange for reassociation,
and the pointed-tensor multiplicativity for the middle-four interchange.  Stated for the next brick. -/
def convertibilityMatrixSoundnessStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (leftDiagram rightDiagram : WireDiagram sourceArity targetArity),
    AreConvertibleDiagrams leftDiagram rightDiagram →
    doEntriesAgreeUpTo targetArity sourceArity (denoteEntries leftDiagram) (denoteEntries rightDiagram)
      = true

/-- RESIDUAL 2 (COMPLETENESS, the harder half): equal matrices imply convertible.  The published route:
canonical forms ([Lafont2003] Sections 2-3: stairs + staircase normal forms, "any diagram reduces to a
canonical form", unique per matrix) or comonoid-then-monoid factorisation ([BSZ2017] Section 2.2 /
[Lack2004] Section 5.3: every diagram factors as a span n <- p -> m, unique up to permutation).  Stated
as the named target of this lane; NOT proven here. -/
def matNatCompletenessStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (leftDiagram rightDiagram : WireDiagram sourceArity targetArity),
    doEntriesAgreeUpTo targetArity sourceArity (denoteEntries leftDiagram) (denoteEntries rightDiagram)
      = true →
    AreConvertibleDiagrams leftDiagram rightDiagram

end FX1Poly.Polygraph.Omega.LafontProp

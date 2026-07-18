import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.FiniteSetSemilatticeSeed

/-! # WalkingDistributiveLattice/DistributiveLatticeSeed — the walking free bounded DISTRIBUTIVE LATTICE on an ARBITRARY alphabet

The two-operation lattice corner of the `n`-colour walker family, following the multiset commutative monoid
(`MultisetCommutativeMonoidSeed`, one operation `m` + unit), the finite-SET bounded semilattice
(`FiniteSetSemilatticeSeed`, one idempotent-commutative operation), and the winding-vector abelian group
(`ColourAbelianGroupSeed`, `{m, e, i}`).  Here the signature is `{∧, ∨, ⊤, ⊥}` closed under the bounded
distributive-lattice laws: meet `∧` and join `∨` are each associative / commutative / idempotent with units
`⊤`/`⊥`, they absorb each other, and meet distributes over join (and, dually, join over meet).

## The canonical form: the minimal-DNF antichain

Every bounded-distributive-lattice term denotes a monotone Boolean function; its canonical form is the
disjunctive normal form — a JOIN of MEETs, written as a SET of generator-CLAUSES (each clause = a
sorted-distinct `List Nat` of generators whose MEET the clause denotes), kept as a ⊆-MINIMAL ANTICHAIN.  In a
join, if `smaller ⊆ bigger` then `meetOfClause bigger ≤ meetOfClause smaller` (meeting more generators is
smaller), so the smaller-set clause ABSORBS the larger-set one — the canonical DNF drops every clause that is a
superset of another.  A clause is a sorted-distinct list built with the imported `insertSortedSet`; clause-union
(the meet of two clauses' meets = the meet over the UNION of their generators) is the imported `insertManySet`.
The encodings are `⊤ ↦ [[]]` (one empty clause = meet of no generators = top, and `[]` ⊆ every clause so top
absorbs everything in a join) and `⊥ ↦ []` (no clauses = the empty join = bottom).

## What this file ships — THE COMPLETE DECISION (round 2: soundness landed, wall SUPERSEDED)

The biconditional `Conv s t ↔ dnfOf s = dnfOf t` is now FULLY CLOSED
(`distributiveLatticeTreeConv_iff_normalForm`), with the Boolean decider `dlDecideConv` and a `Decidable`
instance.  The `⟸` (COMPLETENESS) half is round 1: every tree reduces to the join-of-meets comb of its own
minimal-DNF antichain (`dlTreeReducesToDnfComb`), so equal canonical DNFs are convertible
(`distributiveLatticeTreeConv_complete`) — unblocked by the DL's own absorption law `absorbJoinMeet`
(`dlSupersetAbsorbedInJoin`).  The `⟹` (SOUNDNESS) half `distributiveLatticeTreeConv_sound` is round 2, by
SEMANTIC UNIQUENESS of the minimal-DNF antichain (Quine's unique irredundant DNF of a positive Boolean
function) rather than Conv-invariance of the minimizer: convertible trees agree under every Boolean
environment; each tree evaluates through its canonical DNF (`dlEvalViaDnf`); `dnfOf` output carries three
canonicity invariants (strictly sorted DNF, sorted-distinct clauses, ⊆-antichain); and two canonical DNFs
computing the same monotone function are equal lists (`dlCanonicalDnfUnique`) — membership is read back off
the function at characteristic environments (`dlEvalDnfChar` probes `chi(member)` and
`chi(member \ {missing})`, the antichain forcing prime-implicant minimality).  The former wall marker
`fxWalkingDistributiveLattice_minimizationWall := false` is SUPERSEDED by
`fxWalkingDistributiveLattice_hasNormalFormDecision := true`.

What IS landed, all zero-axiom:

* **the carrier** `LatticeTree` (`gen` / `topOp` / `botOp` / `meetOp` / `joinOp`) and the Boolean-lattice
  evaluation `evalLatticeTree` into the two-element bounded distributive lattice `Bool` (`∧ = &&`, `∨ = ||`,
  `⊤ = true`, `⊥ = false`);
* **the convertibility** `DistributiveLatticeTreeConv` closed under all fourteen distributive-lattice laws plus
  the two congruences and `refl` / `symm` / `trans`;
* **soundness for the semantic invariant** `distributiveLatticeTreeConv_eval_sound` — convertible trees agree
  under every Boolean environment (each law is a finite `Bool` identity), a GENUINE sound separator that
  decides non-convertibility;
* **positive groundings** — distributivity, meet-absorbs-join, and join-absorbs-meet, each by a direct
  convertibility derivation;
* **negative groundings** — distinct generators are inseparable, and (the headline two-operation content) MEET
  and JOIN of two generators genuinely DIFFER, both refuted through `evalLatticeTree` soundness;
* **the DNF normal-form scaffolding** — `genMember` / `clauseSubset` / the clause order, the canonical
  antichain insert `insertClause` (absorb-or-remove-supersets-then-sorted-insert), `dnfUnion` / `dnfMeet` /
  `dnfJoin`, `canonicalizeDnf`, `dnfOf`, `meetOfClause` / `combOfDnf` — computing the canonical minimal-DNF, with
  smokes confirming it SEPARATES meet from join and REFLECTS absorption (`dnfOf (∧ g0 (∨ g0 g1)) = [[0]]`);
* **the absorption lever** — `dlGenMemberMeet` (re-meeting a present generator is idempotent), `dlClauseUnionMeet`
  (`small ⊆ big ⟹ meetOfClause big ≈ meet(meetOfClause small, meetOfClause big)`), and the crux
  `dlSupersetAbsorbedInJoin` (the superset's meet is absorbed in a join by its subset's meet);
* **the comb reduction** — `dlMeetInsertSortedSet` / `dlMeetMergeClause` (the meet-fragment semilattice replay),
  and `dlCombInsertClauseSorted` / `dlHasSubsetAbsorbed` / `dlCombJoinRemoveSupersets` / `dlCombInsertClause` /
  `dlCombDnfUnion` / `dlCombDnfMeetClause` / `dlCombDnfMeet` / `dlCombDnfJoin` — each DNF operation computes the
  tree up to `Conv`;
* **the normalization and COMPLETENESS** — `dlTreeReducesToDnfComb` (`tree ≈ combOfDnf (dnfOf tree)`) and
  `distributiveLatticeTreeConv_complete` (`dnfOf s = dnfOf t → Conv s t`), the `⟸` half of the decision, with
  the completeness groundings `distributiveLatticeCommViaCompleteness` and `distributiveLatticeReductionRoundtrips`;
* **the round-2 SOUNDNESS and the DECISION** — the Boolean DNF evaluation and characteristic-environment
  bridges, the three canonicity invariants of `dnfOf`, the strict clause-order kit (transitivity /
  irreflexivity / asymmetry), prime-implicant membership recovery, canonical-DNF uniqueness,
  `distributiveLatticeTreeConv_sound`, the biconditional `distributiveLatticeTreeConv_iff_normalForm`, the
  decider `dlDecideConv` + `distributiveLatticeTreeConv_iff_decide`, and the `Decidable` instance
  `dlDecidableConv` (see the decision marker at the end of the file for the full round-2 map).

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`
— the ordering is the imported structural `natBle` (no `Nat.le`/`Nat.ble` lemma), the clause inserts are
cons-only, and no `List.append` (`++`) or `Int` appears anywhere. -/

namespace FX1Poly.Polygraph

/-! ## The bounded-distributive-lattice tree carrier over a colour alphabet -/

/-- ★ The **tree carrier** of the walking bounded distributive lattice on an arbitrary alphabet: an un-indexed
tree over colour-indexed generators plus the `{∧, ∨, ⊤, ⊥}` signature.  `gen colour` is a generator tagged with
a colour in `ℕ`; `topOp` is the nullary `⊤` (top / greatest element); `botOp` is the nullary `⊥` (bottom /
least element); `meetOp` grafts under the binary meet `∧`; `joinOp` grafts under the binary join `∨`.  A closed
tree's minimal-DNF antichain is its complete convertibility invariant. -/
inductive LatticeTree where
  /-- A generator tagged with a colour in `ℕ` — an element of the chosen alphabet. -/
  | gen (colour : Nat)
  /-- The nullary generator `⊤` (top). -/
  | topOp
  /-- The nullary generator `⊥` (bottom). -/
  | botOp
  /-- The binary meet `∧` grafting the left and right subtrees (`meet(left, right)`). -/
  | meetOp : LatticeTree → LatticeTree → LatticeTree
  /-- The binary join `∨` grafting the left and right subtrees (`join(left, right)`). -/
  | joinOp : LatticeTree → LatticeTree → LatticeTree

/-! ## The Boolean-lattice evaluation (the sound semantic invariant) -/

/-- **Evaluate a lattice tree into the two-element bounded distributive lattice `Bool`** under a Boolean
environment assigning each colour a truth value: `gen` reads the environment, `topOp ↦ true`, `botOp ↦ false`,
`meetOp ↦ &&` (Boolean meet), `joinOp ↦ ||` (Boolean join).  `Bool` under `(&&, ||, true, false)` satisfies
every distributive-lattice law, so this evaluation is a sound convertibility invariant; a full-enumeration
structural fold, propext-clean. -/
def evalLatticeTree (env : Nat → Bool) : LatticeTree → Bool
  | .gen colour => env colour
  | .topOp => true
  | .botOp => false
  | .meetOp left right => evalLatticeTree env left && evalLatticeTree env right
  | .joinOp left right => evalLatticeTree env left || evalLatticeTree env right

/-- Smoke: a generator evaluates to its environment value. -/
theorem evalLatticeTree_gen (env : Nat → Bool) (colour : Nat) :
    evalLatticeTree env (LatticeTree.gen colour) = env colour := rfl

/-- Smoke: meet evaluates to the Boolean conjunction of the children's values. -/
theorem evalLatticeTree_meet (env : Nat → Bool) (left right : LatticeTree) :
    evalLatticeTree env (LatticeTree.meetOp left right)
      = (evalLatticeTree env left && evalLatticeTree env right) := rfl

/-! ## The bounded-distributive-lattice tree convertibility -/

/-- ★ The **tree convertibility** of the walking bounded distributive lattice on an arbitrary alphabet — the
free convertibility of the `{∧, ∨, ⊤, ⊥}` signature over colour-tagged generators closed under the fourteen
bounded-distributive-lattice laws (meet and join each associative / commutative / idempotent, the four unit
laws, the two absorption laws, and both distributivities), the two congruences `meetCongr` / `joinCongr`, and
`refl` / `symm` / `trans`.  Two trees denote the same element of the free bounded distributive lattice on `ℕ`
exactly when they are `DistributiveLatticeTreeConv`-related. -/
inductive DistributiveLatticeTreeConv : LatticeTree → LatticeTree → Prop where
  /-- **Meet associativity** `meet(meet(left, middle), right) ≈ meet(left, meet(middle, right))`. -/
  | meetAssoc (left middle right : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.meetOp (LatticeTree.meetOp left middle) right)
        (LatticeTree.meetOp left (LatticeTree.meetOp middle right))
  /-- **Meet commutativity** `meet(left, right) ≈ meet(right, left)`. -/
  | meetComm (left right : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.meetOp left right) (LatticeTree.meetOp right left)
  /-- **Meet idempotency** `meet(subtree, subtree) ≈ subtree`. -/
  | meetIdem (subtree : LatticeTree) :
      DistributiveLatticeTreeConv (LatticeTree.meetOp subtree subtree) subtree
  /-- **Join associativity** `join(join(left, middle), right) ≈ join(left, join(middle, right))`. -/
  | joinAssoc (left middle right : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.joinOp (LatticeTree.joinOp left middle) right)
        (LatticeTree.joinOp left (LatticeTree.joinOp middle right))
  /-- **Join commutativity** `join(left, right) ≈ join(right, left)`. -/
  | joinComm (left right : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.joinOp left right) (LatticeTree.joinOp right left)
  /-- **Join idempotency** `join(subtree, subtree) ≈ subtree`. -/
  | joinIdem (subtree : LatticeTree) :
      DistributiveLatticeTreeConv (LatticeTree.joinOp subtree subtree) subtree
  /-- **Meet top unit** `meet(subtree, ⊤) ≈ subtree`. -/
  | meetTop (subtree : LatticeTree) :
      DistributiveLatticeTreeConv (LatticeTree.meetOp subtree LatticeTree.topOp) subtree
  /-- **Join bottom unit** `join(subtree, ⊥) ≈ subtree`. -/
  | joinBot (subtree : LatticeTree) :
      DistributiveLatticeTreeConv (LatticeTree.joinOp subtree LatticeTree.botOp) subtree
  /-- **Meet bottom absorber** `meet(subtree, ⊥) ≈ ⊥`. -/
  | meetBot (subtree : LatticeTree) :
      DistributiveLatticeTreeConv (LatticeTree.meetOp subtree LatticeTree.botOp) LatticeTree.botOp
  /-- **Join top absorber** `join(subtree, ⊤) ≈ ⊤`. -/
  | joinTop (subtree : LatticeTree) :
      DistributiveLatticeTreeConv (LatticeTree.joinOp subtree LatticeTree.topOp) LatticeTree.topOp
  /-- **Meet absorbs join** `meet(base, join(base, other)) ≈ base`. -/
  | absorbMeetJoin (base other : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.meetOp base (LatticeTree.joinOp base other)) base
  /-- **Join absorbs meet** `join(base, meet(base, other)) ≈ base`. -/
  | absorbJoinMeet (base other : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.joinOp base (LatticeTree.meetOp base other)) base
  /-- **Meet distributes over join** `meet(factor, join(left, right)) ≈ join(meet(factor, left), meet(factor,
  right))`. -/
  | distribMeetJoin (factor left right : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.meetOp factor (LatticeTree.joinOp left right))
        (LatticeTree.joinOp (LatticeTree.meetOp factor left) (LatticeTree.meetOp factor right))
  /-- **Join distributes over meet** `join(factor, meet(left, right)) ≈ meet(join(factor, left), join(factor,
  right))` — the dual distributivity (derivable, kept primitive to keep soundness a clean `Bool` identity). -/
  | distribJoinMeet (factor left right : LatticeTree) :
      DistributiveLatticeTreeConv
        (LatticeTree.joinOp factor (LatticeTree.meetOp left right))
        (LatticeTree.meetOp (LatticeTree.joinOp factor left) (LatticeTree.joinOp factor right))
  /-- **Congruence under a meet node** — into BOTH children. -/
  | meetCongr {leftOld leftNew rightOld rightNew : LatticeTree} :
      DistributiveLatticeTreeConv leftOld leftNew → DistributiveLatticeTreeConv rightOld rightNew →
      DistributiveLatticeTreeConv
        (LatticeTree.meetOp leftOld rightOld) (LatticeTree.meetOp leftNew rightNew)
  /-- **Congruence under a join node** — into BOTH children. -/
  | joinCongr {leftOld leftNew rightOld rightNew : LatticeTree} :
      DistributiveLatticeTreeConv leftOld leftNew → DistributiveLatticeTreeConv rightOld rightNew →
      DistributiveLatticeTreeConv
        (LatticeTree.joinOp leftOld rightOld) (LatticeTree.joinOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : LatticeTree) : DistributiveLatticeTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : LatticeTree} :
      DistributiveLatticeTreeConv tree1 tree2 → DistributiveLatticeTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : LatticeTree} :
      DistributiveLatticeTreeConv tree1 tree2 → DistributiveLatticeTreeConv tree2 tree3 →
      DistributiveLatticeTreeConv tree1 tree3

/-! ## Soundness for the Boolean-lattice evaluation -/

/-- ★ **Soundness for the semantic invariant** — convertible trees agree under EVERY Boolean environment.  Each
of the fourteen laws maps to a finite `Bool` identity closed by exhaustive case analysis on the children's
Boolean values (meet `= &&`, join `= ||`, top `= true`, bottom `= false`); the two congruences rewrite by the
inductive hypotheses; `refl` / `symm` / `trans` are `rfl` / `.symm` / `.trans`.  Because `Bool` is a bounded
distributive lattice, this evaluation is a GENUINELY SOUND convertibility invariant — it decides
non-convertibility (used by the negative groundings).  All `Bool` reasoning is propext-clean (`Bool.rec` + `rfl`,
no `decide`-on-`Prop`). -/
theorem distributiveLatticeTreeConv_eval_sound {source target : LatticeTree}
    (conv : DistributiveLatticeTreeConv source target) :
    ∀ env : Nat → Bool, evalLatticeTree env source = evalLatticeTree env target := by
  induction conv with
  | meetAssoc left middle right =>
    intro env
    show ((evalLatticeTree env left && evalLatticeTree env middle) && evalLatticeTree env right)
      = (evalLatticeTree env left && (evalLatticeTree env middle && evalLatticeTree env right))
    cases evalLatticeTree env left <;> cases evalLatticeTree env middle <;>
      cases evalLatticeTree env right <;> rfl
  | meetComm left right =>
    intro env
    show (evalLatticeTree env left && evalLatticeTree env right)
      = (evalLatticeTree env right && evalLatticeTree env left)
    cases evalLatticeTree env left <;> cases evalLatticeTree env right <;> rfl
  | meetIdem subtree =>
    intro env
    show (evalLatticeTree env subtree && evalLatticeTree env subtree) = evalLatticeTree env subtree
    cases evalLatticeTree env subtree <;> rfl
  | joinAssoc left middle right =>
    intro env
    show ((evalLatticeTree env left || evalLatticeTree env middle) || evalLatticeTree env right)
      = (evalLatticeTree env left || (evalLatticeTree env middle || evalLatticeTree env right))
    cases evalLatticeTree env left <;> cases evalLatticeTree env middle <;>
      cases evalLatticeTree env right <;> rfl
  | joinComm left right =>
    intro env
    show (evalLatticeTree env left || evalLatticeTree env right)
      = (evalLatticeTree env right || evalLatticeTree env left)
    cases evalLatticeTree env left <;> cases evalLatticeTree env right <;> rfl
  | joinIdem subtree =>
    intro env
    show (evalLatticeTree env subtree || evalLatticeTree env subtree) = evalLatticeTree env subtree
    cases evalLatticeTree env subtree <;> rfl
  | meetTop subtree =>
    intro env
    show (evalLatticeTree env subtree && true) = evalLatticeTree env subtree
    cases evalLatticeTree env subtree <;> rfl
  | joinBot subtree =>
    intro env
    show (evalLatticeTree env subtree || false) = evalLatticeTree env subtree
    cases evalLatticeTree env subtree <;> rfl
  | meetBot subtree =>
    intro env
    show (evalLatticeTree env subtree && false) = false
    cases evalLatticeTree env subtree <;> rfl
  | joinTop subtree =>
    intro env
    show (evalLatticeTree env subtree || true) = true
    cases evalLatticeTree env subtree <;> rfl
  | absorbMeetJoin base other =>
    intro env
    show (evalLatticeTree env base && (evalLatticeTree env base || evalLatticeTree env other))
      = evalLatticeTree env base
    cases evalLatticeTree env base <;> cases evalLatticeTree env other <;> rfl
  | absorbJoinMeet base other =>
    intro env
    show (evalLatticeTree env base || (evalLatticeTree env base && evalLatticeTree env other))
      = evalLatticeTree env base
    cases evalLatticeTree env base <;> cases evalLatticeTree env other <;> rfl
  | distribMeetJoin factor left right =>
    intro env
    show (evalLatticeTree env factor && (evalLatticeTree env left || evalLatticeTree env right))
      = ((evalLatticeTree env factor && evalLatticeTree env left)
        || (evalLatticeTree env factor && evalLatticeTree env right))
    cases evalLatticeTree env factor <;> cases evalLatticeTree env left <;>
      cases evalLatticeTree env right <;> rfl
  | distribJoinMeet factor left right =>
    intro env
    show (evalLatticeTree env factor || (evalLatticeTree env left && evalLatticeTree env right))
      = ((evalLatticeTree env factor || evalLatticeTree env left)
        && (evalLatticeTree env factor || evalLatticeTree env right))
    cases evalLatticeTree env factor <;> cases evalLatticeTree env left <;>
      cases evalLatticeTree env right <;> rfl
  | @meetCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
    intro env
    show (evalLatticeTree env leftOld && evalLatticeTree env rightOld)
      = (evalLatticeTree env leftNew && evalLatticeTree env rightNew)
    rw [ihLeft env, ihRight env]
  | @joinCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
    intro env
    show (evalLatticeTree env leftOld || evalLatticeTree env rightOld)
      = (evalLatticeTree env leftNew || evalLatticeTree env rightNew)
    rw [ihLeft env, ihRight env]
  | refl tree => intro env; rfl
  | symm _ ih => intro env; exact (ih env).symm
  | trans _ _ ihAB ihBC => intro env; exact (ihAB env).trans (ihBC env)

/-! ## Positive groundings (direct convertibility derivations) -/

/-- ★ **The decision in action (positive, distributivity)** — meet distributes over join across three
generators: `meet(g0, join(g1, g2)) ≈ join(meet(g0, g1), meet(g0, g2))`, by the `distribMeetJoin` law. -/
theorem distributiveLatticeDistributes :
    DistributiveLatticeTreeConv
      (LatticeTree.meetOp (LatticeTree.gen 0)
        (LatticeTree.joinOp (LatticeTree.gen 1) (LatticeTree.gen 2)))
      (LatticeTree.joinOp
        (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1))
        (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 2))) :=
  DistributiveLatticeTreeConv.distribMeetJoin (LatticeTree.gen 0) (LatticeTree.gen 1) (LatticeTree.gen 2)

/-- ★ **The decision in action (positive, meet absorbs join)** — `meet(g0, join(g0, g1)) ≈ g0`, by the
`absorbMeetJoin` law: the two-operation absorption the semilattice cannot express. -/
theorem distributiveLatticeAbsorbs :
    DistributiveLatticeTreeConv
      (LatticeTree.meetOp (LatticeTree.gen 0)
        (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1)))
      (LatticeTree.gen 0) :=
  DistributiveLatticeTreeConv.absorbMeetJoin (LatticeTree.gen 0) (LatticeTree.gen 1)

/-- ★ **The decision in action (positive, join absorbs meet, reordered)** — `join(meet(g0, g1), g0) ≈ g0`:
commute the join, then absorb with `absorbJoinMeet`.  The dual two-operation content. -/
theorem distributiveLatticeJoinMeetAbsorbs :
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp
        (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1))
        (LatticeTree.gen 0))
      (LatticeTree.gen 0) :=
  (DistributiveLatticeTreeConv.joinComm
      (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1)) (LatticeTree.gen 0)).trans
    (DistributiveLatticeTreeConv.absorbJoinMeet (LatticeTree.gen 0) (LatticeTree.gen 1))

/-! ## Negative groundings (refuted through the Boolean-lattice soundness) -/

/-- ★ **The decision in action (negative, distinct generators)** — `g0` is NOT convertible to `g1`: the
environment sending colour `0 ↦ true` and every other colour `↦ false` evaluates `g0` to `true` and `g1` to
`false`, so by `evalLatticeTree` soundness no convertibility can exist.  `Bool.noConfusion`. -/
theorem distributiveLatticeRejectsDistinctGenerators :
    ¬ DistributiveLatticeTreeConv (LatticeTree.gen 0) (LatticeTree.gen 1) := by
  intro conv
  have hEval :=
    distributiveLatticeTreeConv_eval_sound conv (fun colour => Nat.beq colour 0)
  have hAbsurd : (true : Bool) = false := hEval
  exact Bool.noConfusion hAbsurd

/-- ★ **The decision in action (negative, MEET ≠ JOIN — the headline)** — `meet(g0, g1)` is NOT convertible to
`join(g0, g1)`: under the environment `0 ↦ true, 1 ↦ false` the meet evaluates to `true && false = false` while
the join evaluates to `true || false = true`, so by `evalLatticeTree` soundness they separate.  This is the
two-operation content the single-operation semilattice / commutative-monoid walkers structurally cannot see.
`Bool.noConfusion`. -/
theorem distributiveLatticeSeparatesMeetJoin :
    ¬ DistributiveLatticeTreeConv
        (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1))
        (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1)) := by
  intro conv
  have hEval :=
    distributiveLatticeTreeConv_eval_sound conv (fun colour => Nat.beq colour 0)
  have hAbsurd : (false : Bool) = true := hEval
  exact Bool.noConfusion hAbsurd

/-! ## The DNF normal-form scaffolding (canonical minimal antichain; computes, zero-axiom) -/

/-- **Structural membership** of a generator in a clause, by the core Boolean equality `Nat.beq`: scan the
clause for `target`. -/
def genMember (target : Nat) : List Nat → Bool
  | [] => false
  | head :: tail =>
      match Nat.beq head target with
      | true => true
      | false => genMember target tail

/-- **Clause containment** `smaller ⊆ larger` — every generator of `smaller` is a member of `larger`.  The
absorption test: a clause is absorbed by any of its subsets in a join. -/
def clauseSubset : List Nat → List Nat → Bool
  | [], _ => true
  | head :: tail, larger =>
      match genMember head larger with
      | true => clauseSubset tail larger
      | false => false

/-- The **length** of a clause (a purpose-built structural count, avoiding any `List.length` axiom surprise) —
the primary key of the total clause order (shorter clauses first). -/
def clauseLength : List Nat → Nat
  | [] => 0
  | _ :: tail => Nat.succ (clauseLength tail)

/-- **Lexicographic comparison** of two equal-length clauses over the structural `natBle`: `true` when the first
is strictly lexicographically below the second. -/
def clauseLexLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | headA :: tailA, headB :: tailB =>
      match natBle headA headB with
      | false => false
      | true =>
          match natBle headB headA with
          | false => true
          | true => clauseLexLess tailA tailB

/-- The **total clause order** — shorter clauses first (by `clauseLength`), ties broken lexicographically
(`clauseLexLess`).  Used to keep the DNF a sorted-unique list so canonical DNFs compare by structural
`List (List Nat)` equality. -/
def clauseLess (first second : List Nat) : Bool :=
  match natBle (clauseLength first) (clauseLength second) with
  | false => false
  | true =>
      match natBle (clauseLength second) (clauseLength first) with
      | false => true
      | true => clauseLexLess first second

/-- Does the DNF already contain a clause that is `⊆ candidate` (so `candidate` is ABSORBED — a superset of, or
equal to, an existing clause)?  If so, inserting `candidate` is a no-op. -/
def dnfHasSubsetOf (candidate : List Nat) : List (List Nat) → Bool
  | [] => false
  | clause :: rest =>
      match clauseSubset clause candidate with
      | true => true
      | false => dnfHasSubsetOf candidate rest

/-- **Remove every clause that `candidate ⊆` it** (every superset of `candidate`) from the DNF — those clauses
are now absorbed by `candidate` and must go to keep the antichain minimal. -/
def removeSupersets (candidate : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | clause :: rest =>
      match clauseSubset candidate clause with
      | true => removeSupersets candidate rest
      | false => clause :: removeSupersets candidate rest

/-- **Sorted insertion of a clause** into an antichain already ordered by `clauseLess`, placing `candidate`
before the first clause it is `clauseLess` than and collapsing an exact tie (dedup). -/
def insertClauseSorted (candidate : List Nat) : List (List Nat) → List (List Nat)
  | [] => [candidate]
  | clause :: rest =>
      match clauseLess candidate clause with
      | true => candidate :: clause :: rest
      | false =>
          match clauseLess clause candidate with
          | true => clause :: insertClauseSorted candidate rest
          | false => clause :: rest

/-- ★ The **canonical antichain insert** of a clause into a minimal-DNF: if some existing clause is `⊆
candidate` the candidate is absorbed (return the DNF unchanged); otherwise drop every superset of the candidate
and sorted-insert it.  Maintains the sorted-unique ⊆-minimal antichain invariant — the analogue of the finite
set's `insertSortedSet`, now with absorption. -/
def insertClause (candidate : List Nat) (dnf : List (List Nat)) : List (List Nat) :=
  match dnfHasSubsetOf candidate dnf with
  | true => dnf
  | false => insertClauseSorted candidate (removeSupersets candidate dnf)

/-- **Antichain union** — insert every clause of the first DNF into the second, one at a time.  The join of two
minimal-DNFs (the union of their clause sets, re-minimized). -/
def dnfUnion : List (List Nat) → List (List Nat) → List (List Nat)
  | [], acc => acc
  | clause :: rest, acc => insertClause clause (dnfUnion rest acc)

/-- **Canonicalize an arbitrary clause-list** to a minimal-DNF by re-inserting every clause into the empty
antichain — drops non-minimal clauses, dedups, and sorts.  (`dnfOf` already produces canonical output; this is
the standalone minimization.) -/
def canonicalizeDnf : List (List Nat) → List (List Nat)
  | [] => []
  | clause :: rest => insertClause clause (canonicalizeDnf rest)

/-- **Meet one clause against a whole DNF** — for each clause of the DNF, take the generator-union
(`insertManySet`, = the meet of the two clause-meets) and insert it into the antichain. -/
def dnfMeetClause (factor : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | clause :: rest => insertClause (insertManySet factor clause) (dnfMeetClause factor rest)

/-- ★ **DNF meet** — the pairwise generator-union of the clauses of the two DNFs, minimized: distributes the
meet over the two joins.  `dnfMeet [] _ = []` (bottom meet anything is bottom). -/
def dnfMeet : List (List Nat) → List (List Nat) → List (List Nat)
  | [], _ => []
  | clause :: rest, other => dnfUnion (dnfMeetClause clause other) (dnfMeet rest other)

/-- ★ **DNF join** — the antichain union of the two clause-lists (drop every non-minimal clause). -/
def dnfJoin (first second : List (List Nat)) : List (List Nat) := dnfUnion first second

/-- The **meet of a clause's generators** as a tree: `[] ↦ ⊤` (the empty meet), `g :: gs ↦ meet(gen g, ·)`. -/
def meetOfClause : List Nat → LatticeTree
  | [] => LatticeTree.topOp
  | generator :: generators => LatticeTree.meetOp (LatticeTree.gen generator) (meetOfClause generators)

/-- The **join-of-meets tree** of a DNF: `[] ↦ ⊥` (the empty join), `clause :: rest ↦ join(meetOfClause clause,
·)`.  The canonical tree realizing the minimal-DNF antichain. -/
def combOfDnf : List (List Nat) → LatticeTree
  | [] => LatticeTree.botOp
  | clause :: rest => LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)

/-- ★ The **minimal-DNF antichain** of a tree — its canonical form as a sorted-unique list of ⊆-minimal
generator-clauses.  `gen colour ↦ [[colour]]` (the single clause `{colour}`), `topOp ↦ [[]]` (the one empty
clause = `⊤`, which `[] ⊆` every clause so it absorbs everything in a join), `botOp ↦ []` (no clauses = `⊥`),
`meetOp ↦ dnfMeet`, `joinOp ↦ dnfJoin`.  A full-enumeration structural fold, propext-clean. -/
def dnfOf : LatticeTree → List (List Nat)
  | .gen colour => [[colour]]
  | .topOp => [[]]
  | .botOp => []
  | .meetOp left right => dnfMeet (dnfOf left) (dnfOf right)
  | .joinOp left right => dnfJoin (dnfOf left) (dnfOf right)

/-! ## DNF smokes — the normal form computes and SEPARATES the groundings -/

/-- Smoke: a generator's DNF is the single singleton clause. -/
theorem dnfOf_gen : dnfOf (LatticeTree.gen 0) = [[0]] := rfl

/-- Smoke: `⊤` is the single empty clause (the meet of no generators). -/
theorem dnfOf_top : dnfOf LatticeTree.topOp = [[]] := rfl

/-- Smoke: `⊥` is the empty join (no clauses). -/
theorem dnfOf_bot : dnfOf LatticeTree.botOp = [] := rfl

/-- Smoke: the MEET of two generators is the single two-generator clause `{0, 1}`. -/
theorem dnfOf_meetTwoGenerators :
    dnfOf (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1)) = [[0, 1]] := rfl

/-- Smoke: the JOIN of two generators is the two-clause antichain `{ {0}, {1} }` — STRUCTURALLY DIFFERENT from
the meet's `{ {0, 1} }`.  The canonical DNF separates the two operations. -/
theorem dnfOf_joinTwoGenerators :
    dnfOf (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1)) = [[0], [1]] := rfl

/-- Smoke: the canonical DNF REFLECTS absorption — `meet(g0, join(g0, g1))` normalizes to `{ {0} }`, the
minimization dropping the absorbed `{0, 1}` clause, matching `dnfOf g0`.  (The general law that this ALWAYS
holds is the round-2 soundness `distributiveLatticeTreeConv_sound` below; here it is confirmed on the
grounding by kernel computation.) -/
theorem dnfOf_absorbMeetJoin :
    dnfOf (LatticeTree.meetOp (LatticeTree.gen 0)
      (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1))) = [[0]] := rfl

/-- Smoke: `canonicalizeDnf` drops a non-minimal superset clause — `{ {0}, {0, 1} }` minimizes to `{ {0} }`. -/
theorem canonicalizeDnf_dropsSuperset :
    canonicalizeDnf [[0], [0, 1]] = [[0]] := rfl

/-! ## Algebraic convertibility helpers (small derived rewrites) -/

/-- Left meet-unit `meet(⊤, subtree) ≈ subtree` — `meetComm` then the primitive right unit `meetTop`. -/
theorem dlMeetTopLeft (subtree : LatticeTree) :
    DistributiveLatticeTreeConv (LatticeTree.meetOp LatticeTree.topOp subtree) subtree :=
  (DistributiveLatticeTreeConv.meetComm LatticeTree.topOp subtree).trans
    (DistributiveLatticeTreeConv.meetTop subtree)

/-- Left join-unit `join(⊥, subtree) ≈ subtree` — `joinComm` then the primitive right unit `joinBot`. -/
theorem dlJoinBotLeft (subtree : LatticeTree) :
    DistributiveLatticeTreeConv (LatticeTree.joinOp LatticeTree.botOp subtree) subtree :=
  (DistributiveLatticeTreeConv.joinComm LatticeTree.botOp subtree).trans
    (DistributiveLatticeTreeConv.joinBot subtree)

/-- Swap the two front factors of a right-nested meet `meet(first, meet(second, rest)) ≈
meet(second, meet(first, rest))` — reassociate, commute the pair, reassociate back. -/
theorem dlMeetSwapFront (first second rest : LatticeTree) :
    DistributiveLatticeTreeConv
      (LatticeTree.meetOp first (LatticeTree.meetOp second rest))
      (LatticeTree.meetOp second (LatticeTree.meetOp first rest)) :=
  (DistributiveLatticeTreeConv.meetAssoc first second rest).symm.trans
    ((DistributiveLatticeTreeConv.meetCongr (DistributiveLatticeTreeConv.meetComm first second)
        (DistributiveLatticeTreeConv.refl rest)).trans
      (DistributiveLatticeTreeConv.meetAssoc second first rest))

/-- Swap the two front summands of a right-nested join `join(first, join(second, rest)) ≈
join(second, join(first, rest))`. -/
theorem dlJoinSwapFront (first second rest : LatticeTree) :
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp first (LatticeTree.joinOp second rest))
      (LatticeTree.joinOp second (LatticeTree.joinOp first rest)) :=
  (DistributiveLatticeTreeConv.joinAssoc first second rest).symm.trans
    ((DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.joinComm first second)
        (DistributiveLatticeTreeConv.refl rest)).trans
      (DistributiveLatticeTreeConv.joinAssoc second first rest))

/-- Collapse a duplicate front meet-factor `meet(elem, meet(elem, rest)) ≈ meet(elem, rest)` — reassociate,
then `meetIdem`. -/
theorem dlMeetIdemFront (elem rest : LatticeTree) :
    DistributiveLatticeTreeConv
      (LatticeTree.meetOp elem (LatticeTree.meetOp elem rest))
      (LatticeTree.meetOp elem rest) :=
  (DistributiveLatticeTreeConv.meetAssoc elem elem rest).symm.trans
    (DistributiveLatticeTreeConv.meetCongr (DistributiveLatticeTreeConv.meetIdem elem)
      (DistributiveLatticeTreeConv.refl rest))

/-- Collapse a duplicate front join-summand `join(elem, join(elem, rest)) ≈ join(elem, rest)`. -/
theorem dlJoinIdemFront (elem rest : LatticeTree) :
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp elem (LatticeTree.joinOp elem rest))
      (LatticeTree.joinOp elem rest) :=
  (DistributiveLatticeTreeConv.joinAssoc elem elem rest).symm.trans
    (DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.joinIdem elem)
      (DistributiveLatticeTreeConv.refl rest))

/-- Right distributivity of meet over join `meet(join(left, right), factor) ≈
join(meet(left, factor), meet(right, factor))` — derived from the primitive left distributivity by
commuting the outer and inner meets. -/
theorem dlMeetJoinRightDistrib (left right factor : LatticeTree) :
    DistributiveLatticeTreeConv
      (LatticeTree.meetOp (LatticeTree.joinOp left right) factor)
      (LatticeTree.joinOp (LatticeTree.meetOp left factor) (LatticeTree.meetOp right factor)) :=
  (DistributiveLatticeTreeConv.meetComm (LatticeTree.joinOp left right) factor).trans
    ((DistributiveLatticeTreeConv.distribMeetJoin factor left right).trans
      (DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.meetComm factor left)
        (DistributiveLatticeTreeConv.meetComm factor right)))

/-! ## Structural equation lemmas for the DNF-scaffolding matches -/

/-- If `Nat.beq first second = true` then `first = second` — a self-contained structural converse
(avoids any propext-leaky library `Nat.eq_of_beq_eq_true`). -/
theorem dlNatBeqEq : (first second : Nat) → Nat.beq first second = true → first = second
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => Bool.noConfusion h
  | Nat.succ _, 0, h => Bool.noConfusion h
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, h =>
      congrArg Nat.succ (dlNatBeqEq firstPredecessor secondPredecessor h)

/-- `genMember` cons equation (MISS): when the head is not the target the search recurses. -/
theorem dlGenMemberConsFalse (target head : Nat) (tail : List Nat)
    (h : Nat.beq head target = false) :
    genMember target (head :: tail) = genMember target tail := by
  show (match Nat.beq head target with
        | true => true
        | false => genMember target tail) = genMember target tail
  rw [h]

/-- `clauseSubset` cons equation (HEAD PRESENT): when the head is a member of `larger`, containment
recurses on the tail. -/
theorem dlClauseSubsetConsMem (head : Nat) (tail larger : List Nat)
    (h : genMember head larger = true) :
    clauseSubset (head :: tail) larger = clauseSubset tail larger := by
  show (match genMember head larger with
        | true => clauseSubset tail larger
        | false => false) = clauseSubset tail larger
  rw [h]

/-- `clauseSubset` cons equation (HEAD ABSENT): a missing head refutes containment. -/
theorem dlClauseSubsetConsFalse (head : Nat) (tail larger : List Nat)
    (h : genMember head larger = false) :
    clauseSubset (head :: tail) larger = false := by
  show (match genMember head larger with
        | true => clauseSubset tail larger
        | false => false) = false
  rw [h]

/-- `clauseLexLess` cons equation (GREATER head): a strictly greater head refutes lex-below. -/
theorem dlClauseLexGt (headA headB : Nat) (tailA tailB : List Nat)
    (h : natBle headA headB = false) :
    clauseLexLess (headA :: tailA) (headB :: tailB) = false := by
  show (match natBle headA headB with
        | false => false
        | true =>
            match natBle headB headA with
            | false => true
            | true => clauseLexLess tailA tailB) = false
  rw [h]

/-- `clauseLexLess` cons equation (LESS head): a strictly smaller head witnesses lex-below. -/
theorem dlClauseLexLt (headA headB : Nat) (tailA tailB : List Nat)
    (hle : natBle headA headB = true) (hgt : natBle headB headA = false) :
    clauseLexLess (headA :: tailA) (headB :: tailB) = true := by
  show (match natBle headA headB with
        | false => false
        | true =>
            match natBle headB headA with
            | false => true
            | true => clauseLexLess tailA tailB) = true
  rw [hle, hgt]

/-- `clauseLexLess` cons equation (EQUAL head): equal heads defer the comparison to the tails. -/
theorem dlClauseLexEqStep (headA headB : Nat) (tailA tailB : List Nat)
    (hle : natBle headA headB = true) (hge : natBle headB headA = true) :
    clauseLexLess (headA :: tailA) (headB :: tailB) = clauseLexLess tailA tailB := by
  show (match natBle headA headB with
        | false => false
        | true =>
            match natBle headB headA with
            | false => true
            | true => clauseLexLess tailA tailB) = clauseLexLess tailA tailB
  rw [hle, hge]

/-- **Antisymmetry of `clauseLexLess`** — two equal-length-comparable clauses each not lex-below the other
are equal.  Induction on the first list (generalizing the second); the head order splits LESS / EQUAL /
GREATER via `natBleTotal` and `natBleAntisymm`. -/
theorem dlClauseLexAntisymm (first : List Nat) : (second : List Nat) →
    clauseLexLess first second = false → clauseLexLess second first = false → first = second := by
  induction first with
  | nil =>
    intro second h1 h2
    cases second with
    | nil => rfl
    | cons headB tailB => exact Bool.noConfusion h1
  | cons headA tailA ih =>
    intro second h1 h2
    cases second with
    | nil => exact Bool.noConfusion h2
    | cons headB tailB =>
      cases hAB : natBle headA headB with
      | false =>
        have hBA : natBle headB headA = true := natBleTotal headA headB hAB
        rw [dlClauseLexLt headB headA tailB tailA hBA hAB] at h2
        exact Bool.noConfusion h2
      | true =>
        cases hBA : natBle headB headA with
        | false =>
          rw [dlClauseLexLt headA headB tailA tailB hAB hBA] at h1
          exact Bool.noConfusion h1
        | true =>
          have hHead : headA = headB := natBleAntisymm headA headB hAB hBA
          rw [dlClauseLexEqStep headA headB tailA tailB hAB hBA] at h1
          rw [dlClauseLexEqStep headB headA tailB tailA hBA hAB] at h2
          have hTail : tailA = tailB := ih tailB h1 h2
          rw [hHead, hTail]

/-- `clauseLess` equation (STRICTLY SHORTER first): a first clause of strictly smaller length is below. -/
theorem dlClauseLessLt (first second : List Nat)
    (hle : natBle (clauseLength first) (clauseLength second) = true)
    (hgt : natBle (clauseLength second) (clauseLength first) = false) :
    clauseLess first second = true := by
  show (match natBle (clauseLength first) (clauseLength second) with
        | false => false
        | true =>
            match natBle (clauseLength second) (clauseLength first) with
            | false => true
            | true => clauseLexLess first second) = true
  rw [hle, hgt]

/-- `clauseLess` equation (EQUAL length): equal lengths defer the order to the lexicographic comparison. -/
theorem dlClauseLessEqStep (first second : List Nat)
    (hle : natBle (clauseLength first) (clauseLength second) = true)
    (hge : natBle (clauseLength second) (clauseLength first) = true) :
    clauseLess first second = clauseLexLess first second := by
  show (match natBle (clauseLength first) (clauseLength second) with
        | false => false
        | true =>
            match natBle (clauseLength second) (clauseLength first) with
            | false => true
            | true => clauseLexLess first second) = clauseLexLess first second
  rw [hle, hge]

/-- **Antisymmetry of the total clause order** — a tie in `clauseLess` (neither below the other) forces
equality.  Length comparison first (via `natBleTotal`), then `dlClauseLexAntisymm`.  Used to justify the
dedup no-op branch of `insertClauseSorted`. -/
theorem dlClauseLessAntisymm (first second : List Nat)
    (h1 : clauseLess first second = false) (h2 : clauseLess second first = false) :
    first = second := by
  cases hLenAB : natBle (clauseLength first) (clauseLength second) with
  | false =>
    have hLenBA : natBle (clauseLength second) (clauseLength first) = true :=
      natBleTotal (clauseLength first) (clauseLength second) hLenAB
    rw [dlClauseLessLt second first hLenBA hLenAB] at h2
    exact Bool.noConfusion h2
  | true =>
    cases hLenBA : natBle (clauseLength second) (clauseLength first) with
    | false =>
      rw [dlClauseLessLt first second hLenAB hLenBA] at h1
      exact Bool.noConfusion h1
    | true =>
      rw [dlClauseLessEqStep first second hLenAB hLenBA] at h1
      rw [dlClauseLessEqStep second first hLenBA hLenAB] at h2
      exact dlClauseLexAntisymm first second h1 h2

/-! ## The meet fragment normalization (replaying the semilattice comb for `meetOfClause`) -/

/-- Inserting a generator into a sorted-distinct clause is convertible to grafting its meet on the front,
COLLAPSING by `meetIdem` when the generator is already present.  The meet-fragment analogue of
`combInsertSortedSet`: `meetOp` is associative / commutative / idempotent with unit `⊤`. -/
theorem dlMeetInsertSortedSet (colour : Nat) (xs : List Nat) :
    DistributiveLatticeTreeConv (meetOfClause (insertSortedSet colour xs))
      (LatticeTree.meetOp (LatticeTree.gen colour) (meetOfClause xs)) := by
  induction xs with
  | nil => exact DistributiveLatticeTreeConv.refl _
  | cons head rest ih =>
    cases hCH : natBle colour head with
    | true =>
      cases hHC : natBle head colour with
      | true =>
        rw [insertSortedSetEq colour head rest hCH hHC]
        have hEq : colour = head := natBleAntisymm colour head hCH hHC
        rw [hEq]
        exact DistributiveLatticeTreeConv.symm
          (DistributiveLatticeTreeConv.trans
            (DistributiveLatticeTreeConv.symm
              (DistributiveLatticeTreeConv.meetAssoc (LatticeTree.gen head) (LatticeTree.gen head)
                (meetOfClause rest)))
            (DistributiveLatticeTreeConv.meetCongr
              (DistributiveLatticeTreeConv.meetIdem (LatticeTree.gen head))
              (DistributiveLatticeTreeConv.refl (meetOfClause rest))))
      | false =>
        rw [insertSortedSetLt colour head rest hCH hHC]
        exact DistributiveLatticeTreeConv.refl _
    | false =>
      rw [insertSortedSetGt colour head rest hCH]
      exact
        (DistributiveLatticeTreeConv.meetCongr
            (DistributiveLatticeTreeConv.refl (LatticeTree.gen head)) ih).trans
          ((DistributiveLatticeTreeConv.symm
              (DistributiveLatticeTreeConv.meetAssoc (LatticeTree.gen head) (LatticeTree.gen colour)
                (meetOfClause rest))).trans
            ((DistributiveLatticeTreeConv.meetCongr
                (DistributiveLatticeTreeConv.meetComm (LatticeTree.gen head) (LatticeTree.gen colour))
                (DistributiveLatticeTreeConv.refl (meetOfClause rest))).trans
              (DistributiveLatticeTreeConv.meetAssoc (LatticeTree.gen colour) (LatticeTree.gen head)
                (meetOfClause rest))))

/-- ★ **The generator-union meet** — `meetOfClause (insertManySet first second)` (the meet over the set-union
of the two clauses' generators) is convertible to `meet(meetOfClause first, meetOfClause second)`.  The
meet-fragment analogue of `combMergeSet`; the reverse direction realizes `dnfMeetClause`'s clause union. -/
theorem dlMeetMergeClause (xs ys : List Nat) :
    DistributiveLatticeTreeConv (LatticeTree.meetOp (meetOfClause xs) (meetOfClause ys))
      (meetOfClause (insertManySet xs ys)) := by
  induction xs with
  | nil => exact dlMeetTopLeft (meetOfClause ys)
  | cons head tail ih =>
    exact
      (DistributiveLatticeTreeConv.meetAssoc (LatticeTree.gen head) (meetOfClause tail)
          (meetOfClause ys)).trans
        ((DistributiveLatticeTreeConv.meetCongr (DistributiveLatticeTreeConv.refl (LatticeTree.gen head))
            ih).trans
          (DistributiveLatticeTreeConv.symm (dlMeetInsertSortedSet head (insertManySet tail ys))))

/-! ## The absorption lever (the antichain-minimization crux) -/

/-- If a generator is a member of a clause, re-meeting it is idempotent:
`meetOfClause clause ≈ meet(gen generator, meetOfClause clause)`.  Induction on the clause; the present-head
case collapses by `dlMeetIdemFront`, the recurse case bubbles the generator to the front by `dlMeetSwapFront`. -/
theorem dlGenMemberMeet (generator : Nat) : (clause : List Nat) →
    genMember generator clause = true →
    DistributiveLatticeTreeConv (meetOfClause clause)
      (LatticeTree.meetOp (LatticeTree.gen generator) (meetOfClause clause)) := by
  intro clause
  induction clause with
  | nil => intro h; exact Bool.noConfusion h
  | cons head hs ih =>
    intro h
    cases hb : Nat.beq head generator with
    | true =>
      have hEq : head = generator := dlNatBeqEq head generator hb
      show DistributiveLatticeTreeConv (LatticeTree.meetOp (LatticeTree.gen head) (meetOfClause hs))
        (LatticeTree.meetOp (LatticeTree.gen generator)
          (LatticeTree.meetOp (LatticeTree.gen head) (meetOfClause hs)))
      rw [← hEq]
      exact (dlMeetIdemFront (LatticeTree.gen head) (meetOfClause hs)).symm
    | false =>
      have hRec : genMember generator hs = true := by
        rw [dlGenMemberConsFalse generator head hs hb] at h
        exact h
      have ihApplied := ih hRec
      show DistributiveLatticeTreeConv (LatticeTree.meetOp (LatticeTree.gen head) (meetOfClause hs))
        (LatticeTree.meetOp (LatticeTree.gen generator)
          (LatticeTree.meetOp (LatticeTree.gen head) (meetOfClause hs)))
      exact (DistributiveLatticeTreeConv.meetCongr
          (DistributiveLatticeTreeConv.refl (LatticeTree.gen head)) ihApplied).trans
        (dlMeetSwapFront (LatticeTree.gen head) (LatticeTree.gen generator) (meetOfClause hs))

/-- ★ **The subset re-meet lemma (STEP 1a)** — if `small ⊆ big` then meeting `big` again with `small`'s meet
changes nothing: `meetOfClause big ≈ meet(meetOfClause small, meetOfClause big)`.  Each generator of `small` is
already in `big`, so re-meeting is idempotent (`dlGenMemberMeet`); induction on `small`. -/
theorem dlClauseUnionMeet (big : List Nat) : (small : List Nat) →
    clauseSubset small big = true →
    DistributiveLatticeTreeConv (meetOfClause big)
      (LatticeTree.meetOp (meetOfClause small) (meetOfClause big)) := by
  intro small
  induction small with
  | nil =>
    intro _
    exact (dlMeetTopLeft (meetOfClause big)).symm
  | cons g gs ih =>
    intro h
    cases hMem : genMember g big with
    | false =>
      rw [dlClauseSubsetConsFalse g gs big hMem] at h
      exact Bool.noConfusion h
    | true =>
      have hSub : clauseSubset gs big = true := by
        rw [dlClauseSubsetConsMem g gs big hMem] at h
        exact h
      have ihApplied := ih hSub
      have hGen := dlGenMemberMeet g big hMem
      show DistributiveLatticeTreeConv (meetOfClause big)
        (LatticeTree.meetOp (LatticeTree.meetOp (LatticeTree.gen g) (meetOfClause gs)) (meetOfClause big))
      exact hGen.trans
        ((DistributiveLatticeTreeConv.meetCongr (DistributiveLatticeTreeConv.refl (LatticeTree.gen g))
            ihApplied).trans
          (DistributiveLatticeTreeConv.meetAssoc (LatticeTree.gen g) (meetOfClause gs)
            (meetOfClause big)).symm)

/-- ★ **The superset absorption lemma (STEP 1b — the lever)** — if `small ⊆ big` then in a join the
`big`-clause's meet is ABSORBED by the `small`-clause's meet: `join(meetOfClause small, meetOfClause big) ≈
meetOfClause small`.  Rewrite `meetOfClause big` by STEP 1a, then fire the DL's own `absorbJoinMeet`.  This is
exactly what makes the antichain minimization convertibility-invariant. -/
theorem dlSupersetAbsorbedInJoin (small big : List Nat) (h : clauseSubset small big = true) :
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp (meetOfClause small) (meetOfClause big)) (meetOfClause small) :=
  (DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.refl (meetOfClause small))
      (dlClauseUnionMeet big small h)).trans
    (DistributiveLatticeTreeConv.absorbJoinMeet (meetOfClause small) (meetOfClause big))

/-! ## Structural equation lemmas for the antichain-insert matches -/

/-- `dnfHasSubsetOf` cons equation (HIT): an existing subset of the candidate reports absorption. -/
theorem dlHasSubsetConsTrue (candidate clause : List Nat) (rest : List (List Nat))
    (h : clauseSubset clause candidate = true) :
    dnfHasSubsetOf candidate (clause :: rest) = true := by
  show (match clauseSubset clause candidate with
        | true => true
        | false => dnfHasSubsetOf candidate rest) = true
  rw [h]

/-- `dnfHasSubsetOf` cons equation (MISS): a non-subset head defers to the rest. -/
theorem dlHasSubsetConsFalse (candidate clause : List Nat) (rest : List (List Nat))
    (h : clauseSubset clause candidate = false) :
    dnfHasSubsetOf candidate (clause :: rest) = dnfHasSubsetOf candidate rest := by
  show (match clauseSubset clause candidate with
        | true => true
        | false => dnfHasSubsetOf candidate rest) = dnfHasSubsetOf candidate rest
  rw [h]

/-- `removeSupersets` cons equation (DROP): a clause that contains the candidate is a superset and removed. -/
theorem dlRemoveSupersetsConsDrop (candidate clause : List Nat) (rest : List (List Nat))
    (h : clauseSubset candidate clause = true) :
    removeSupersets candidate (clause :: rest) = removeSupersets candidate rest := by
  show (match clauseSubset candidate clause with
        | true => removeSupersets candidate rest
        | false => clause :: removeSupersets candidate rest) = removeSupersets candidate rest
  rw [h]

/-- `removeSupersets` cons equation (KEEP): a clause not containing the candidate survives. -/
theorem dlRemoveSupersetsConsKeep (candidate clause : List Nat) (rest : List (List Nat))
    (h : clauseSubset candidate clause = false) :
    removeSupersets candidate (clause :: rest) = clause :: removeSupersets candidate rest := by
  show (match clauseSubset candidate clause with
        | true => removeSupersets candidate rest
        | false => clause :: removeSupersets candidate rest) = clause :: removeSupersets candidate rest
  rw [h]

/-- `insertClauseSorted` cons equation (FRONT): a candidate below the head lands at the front. -/
theorem dlInsertClauseSortedLt (candidate clause : List Nat) (rest : List (List Nat))
    (h : clauseLess candidate clause = true) :
    insertClauseSorted candidate (clause :: rest) = candidate :: clause :: rest := by
  show (match clauseLess candidate clause with
        | true => candidate :: clause :: rest
        | false =>
            match clauseLess clause candidate with
            | true => clause :: insertClauseSorted candidate rest
            | false => clause :: rest) = candidate :: clause :: rest
  rw [h]

/-- `insertClauseSorted` cons equation (RECURSE): a candidate strictly above the head recurses past it. -/
theorem dlInsertClauseSortedGt (candidate clause : List Nat) (rest : List (List Nat))
    (hlt : clauseLess candidate clause = false) (hgt : clauseLess clause candidate = true) :
    insertClauseSorted candidate (clause :: rest) = clause :: insertClauseSorted candidate rest := by
  show (match clauseLess candidate clause with
        | true => candidate :: clause :: rest
        | false =>
            match clauseLess clause candidate with
            | true => clause :: insertClauseSorted candidate rest
            | false => clause :: rest) = clause :: insertClauseSorted candidate rest
  rw [hlt, hgt]

/-- `insertClauseSorted` cons equation (DEDUP): an order-tie with the head collapses (candidate dropped). -/
theorem dlInsertClauseSortedEq (candidate clause : List Nat) (rest : List (List Nat))
    (hlt : clauseLess candidate clause = false) (hgt : clauseLess clause candidate = false) :
    insertClauseSorted candidate (clause :: rest) = clause :: rest := by
  show (match clauseLess candidate clause with
        | true => candidate :: clause :: rest
        | false =>
            match clauseLess clause candidate with
            | true => clause :: insertClauseSorted candidate rest
            | false => clause :: rest) = clause :: rest
  rw [hlt, hgt]

/-- `insertClause` equation (ABSORBED): a candidate whose subset is already present is a no-op. -/
theorem dlInsertClauseAbsorbed (candidate : List Nat) (dnf : List (List Nat))
    (h : dnfHasSubsetOf candidate dnf = true) : insertClause candidate dnf = dnf := by
  show (match dnfHasSubsetOf candidate dnf with
        | true => dnf
        | false => insertClauseSorted candidate (removeSupersets candidate dnf)) = dnf
  rw [h]

/-- `insertClause` equation (FRESH): a non-absorbed candidate drops supersets then sorted-inserts. -/
theorem dlInsertClauseFresh (candidate : List Nat) (dnf : List (List Nat))
    (h : dnfHasSubsetOf candidate dnf = false) :
    insertClause candidate dnf = insertClauseSorted candidate (removeSupersets candidate dnf) := by
  show (match dnfHasSubsetOf candidate dnf with
        | true => dnf
        | false => insertClauseSorted candidate (removeSupersets candidate dnf))
      = insertClauseSorted candidate (removeSupersets candidate dnf)
  rw [h]

/-! ## The comb reduction lemmas (STEP 3: the DNF operations compute the tree up to Conv) -/

/-- **Sorted clause insert = join on the front** — `combOfDnf (insertClauseSorted candidate dnf) ≈
join(meetOfClause candidate, combOfDnf dnf)`.  Pure reordering in the join (`dlJoinSwapFront`); the dedup tie
collapses by `dlJoinIdemFront` using order antisymmetry (`dlClauseLessAntisymm`). -/
theorem dlCombInsertClauseSorted (candidate : List Nat) (dnf : List (List Nat)) :
    DistributiveLatticeTreeConv (combOfDnf (insertClauseSorted candidate dnf))
      (LatticeTree.joinOp (meetOfClause candidate) (combOfDnf dnf)) := by
  induction dnf with
  | nil => exact DistributiveLatticeTreeConv.refl _
  | cons clause rest ih =>
    cases hLt : clauseLess candidate clause with
    | true =>
      rw [dlInsertClauseSortedLt candidate clause rest hLt]
      exact DistributiveLatticeTreeConv.refl _
    | false =>
      cases hGt : clauseLess clause candidate with
      | true =>
        rw [dlInsertClauseSortedGt candidate clause rest hLt hGt]
        show DistributiveLatticeTreeConv
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf (insertClauseSorted candidate rest)))
          (LatticeTree.joinOp (meetOfClause candidate)
            (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)))
        exact (DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.refl (meetOfClause clause))
            ih).trans
          (dlJoinSwapFront (meetOfClause clause) (meetOfClause candidate) (combOfDnf rest))
      | false =>
        rw [dlInsertClauseSortedEq candidate clause rest hLt hGt]
        have hEq : candidate = clause := dlClauseLessAntisymm candidate clause hLt hGt
        show DistributiveLatticeTreeConv
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest))
          (LatticeTree.joinOp (meetOfClause candidate)
            (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)))
        rw [hEq]
        exact (dlJoinIdemFront (meetOfClause clause) (combOfDnf rest)).symm

/-- **An absorbed candidate joins away** — if some existing clause is `⊆ candidate` then
`join(meetOfClause candidate, combOfDnf dnf) ≈ combOfDnf dnf`.  Induction on the DNF: the covering clause
absorbs the candidate by `dlSupersetAbsorbedInJoin`, else the candidate bubbles past by `dlJoinSwapFront`. -/
theorem dlHasSubsetAbsorbed (candidate : List Nat) : (dnf : List (List Nat)) →
    dnfHasSubsetOf candidate dnf = true →
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp (meetOfClause candidate) (combOfDnf dnf)) (combOfDnf dnf) := by
  intro dnf
  induction dnf with
  | nil => intro h; exact Bool.noConfusion h
  | cons clause rest ih =>
    intro h
    cases hSub : clauseSubset clause candidate with
    | true =>
      show DistributiveLatticeTreeConv
        (LatticeTree.joinOp (meetOfClause candidate)
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)))
        (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest))
      exact
        (DistributiveLatticeTreeConv.joinAssoc (meetOfClause candidate) (meetOfClause clause)
            (combOfDnf rest)).symm.trans
          (DistributiveLatticeTreeConv.joinCongr
            ((DistributiveLatticeTreeConv.joinComm (meetOfClause candidate) (meetOfClause clause)).trans
              (dlSupersetAbsorbedInJoin clause candidate hSub))
            (DistributiveLatticeTreeConv.refl (combOfDnf rest)))
    | false =>
      have hRec : dnfHasSubsetOf candidate rest = true := by
        rw [dlHasSubsetConsFalse candidate clause rest hSub] at h
        exact h
      have ihApplied := ih hRec
      show DistributiveLatticeTreeConv
        (LatticeTree.joinOp (meetOfClause candidate)
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)))
        (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest))
      exact (dlJoinSwapFront (meetOfClause candidate) (meetOfClause clause) (combOfDnf rest)).trans
        (DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.refl (meetOfClause clause))
          ihApplied)

/-- **Dropping supersets is join-invariant under the candidate** —
`join(meetOfClause candidate, combOfDnf (removeSupersets candidate dnf)) ≈
join(meetOfClause candidate, combOfDnf dnf)`.  Each dropped superset is re-absorbed by the candidate
(`dlSupersetAbsorbedInJoin`); kept clauses recurse through `dlJoinSwapFront`. -/
theorem dlCombJoinRemoveSupersets (candidate : List Nat) (dnf : List (List Nat)) :
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp (meetOfClause candidate) (combOfDnf (removeSupersets candidate dnf)))
      (LatticeTree.joinOp (meetOfClause candidate) (combOfDnf dnf)) := by
  induction dnf with
  | nil => exact DistributiveLatticeTreeConv.refl _
  | cons clause rest ih =>
    cases hSub : clauseSubset candidate clause with
    | true =>
      rw [dlRemoveSupersetsConsDrop candidate clause rest hSub]
      show DistributiveLatticeTreeConv
        (LatticeTree.joinOp (meetOfClause candidate) (combOfDnf (removeSupersets candidate rest)))
        (LatticeTree.joinOp (meetOfClause candidate)
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)))
      refine ih.trans ?_
      exact DistributiveLatticeTreeConv.symm
        ((DistributiveLatticeTreeConv.joinAssoc (meetOfClause candidate) (meetOfClause clause)
            (combOfDnf rest)).symm.trans
          (DistributiveLatticeTreeConv.joinCongr
            (dlSupersetAbsorbedInJoin candidate clause hSub)
            (DistributiveLatticeTreeConv.refl (combOfDnf rest))))
    | false =>
      rw [dlRemoveSupersetsConsKeep candidate clause rest hSub]
      show DistributiveLatticeTreeConv
        (LatticeTree.joinOp (meetOfClause candidate)
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf (removeSupersets candidate rest))))
        (LatticeTree.joinOp (meetOfClause candidate)
          (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)))
      exact (dlJoinSwapFront (meetOfClause candidate) (meetOfClause clause)
            (combOfDnf (removeSupersets candidate rest))).trans
        ((DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.refl (meetOfClause clause))
            ih).trans
          (dlJoinSwapFront (meetOfClause clause) (meetOfClause candidate) (combOfDnf rest)))

/-- ★ **The antichain insert computes the join** — `combOfDnf (insertClause candidate dnf) ≈
join(meetOfClause candidate, combOfDnf dnf)`.  The absorbed case is `dlHasSubsetAbsorbed`; the fresh case is
`dlCombInsertClauseSorted` after `dlCombJoinRemoveSupersets`. -/
theorem dlCombInsertClause (candidate : List Nat) (dnf : List (List Nat)) :
    DistributiveLatticeTreeConv (combOfDnf (insertClause candidate dnf))
      (LatticeTree.joinOp (meetOfClause candidate) (combOfDnf dnf)) := by
  cases hHas : dnfHasSubsetOf candidate dnf with
  | true =>
    rw [dlInsertClauseAbsorbed candidate dnf hHas]
    exact (dlHasSubsetAbsorbed candidate dnf hHas).symm
  | false =>
    rw [dlInsertClauseFresh candidate dnf hHas]
    exact (dlCombInsertClauseSorted candidate (removeSupersets candidate dnf)).trans
      (dlCombJoinRemoveSupersets candidate dnf)

/-- ★ **DNF union computes the join** — `combOfDnf (dnfUnion first second) ≈ join(combOfDnf first,
combOfDnf second)`.  Induction on `first`, inserting each clause via `dlCombInsertClause` and re-associating. -/
theorem dlCombDnfUnion (first second : List (List Nat)) :
    DistributiveLatticeTreeConv (combOfDnf (dnfUnion first second))
      (LatticeTree.joinOp (combOfDnf first) (combOfDnf second)) := by
  induction first with
  | nil => exact (dlJoinBotLeft (combOfDnf second)).symm
  | cons clause rest ih =>
    show DistributiveLatticeTreeConv (combOfDnf (insertClause clause (dnfUnion rest second)))
      (LatticeTree.joinOp (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)) (combOfDnf second))
    exact (dlCombInsertClause clause (dnfUnion rest second)).trans
      ((DistributiveLatticeTreeConv.joinCongr (DistributiveLatticeTreeConv.refl (meetOfClause clause))
          ih).trans
        (DistributiveLatticeTreeConv.joinAssoc (meetOfClause clause) (combOfDnf rest)
          (combOfDnf second)).symm)

/-- **Meet one clause against a DNF, computed** — `combOfDnf (dnfMeetClause clause other) ≈
meet(meetOfClause clause, combOfDnf other)`.  Distributes the clause-meet over the DNF's join
(`distribMeetJoin`), the clause union realized by `dlMeetMergeClause`. -/
theorem dlCombDnfMeetClause (clause : List Nat) (other : List (List Nat)) :
    DistributiveLatticeTreeConv (combOfDnf (dnfMeetClause clause other))
      (LatticeTree.meetOp (meetOfClause clause) (combOfDnf other)) := by
  induction other with
  | nil => exact (DistributiveLatticeTreeConv.meetBot (meetOfClause clause)).symm
  | cons c rest ih =>
    show DistributiveLatticeTreeConv
      (combOfDnf (insertClause (insertManySet clause c) (dnfMeetClause clause rest)))
      (LatticeTree.meetOp (meetOfClause clause)
        (LatticeTree.joinOp (meetOfClause c) (combOfDnf rest)))
    refine (dlCombInsertClause (insertManySet clause c) (dnfMeetClause clause rest)).trans ?_
    refine (DistributiveLatticeTreeConv.joinCongr (dlMeetMergeClause clause c).symm ih).trans ?_
    exact (DistributiveLatticeTreeConv.distribMeetJoin (meetOfClause clause) (meetOfClause c)
      (combOfDnf rest)).symm

/-- ★ **DNF meet computes the meet** — `combOfDnf (dnfMeet first second) ≈ meet(combOfDnf first,
combOfDnf second)`.  Induction on `first`; each head clause distributes on the right
(`dlMeetJoinRightDistrib`) matching the pairwise-union structure of `dnfMeet`. -/
theorem dlCombDnfMeet (first second : List (List Nat)) :
    DistributiveLatticeTreeConv (combOfDnf (dnfMeet first second))
      (LatticeTree.meetOp (combOfDnf first) (combOfDnf second)) := by
  induction first with
  | nil =>
    exact DistributiveLatticeTreeConv.symm
      ((DistributiveLatticeTreeConv.meetComm LatticeTree.botOp (combOfDnf second)).trans
        (DistributiveLatticeTreeConv.meetBot (combOfDnf second)))
  | cons clause rest ih =>
    show DistributiveLatticeTreeConv
      (combOfDnf (dnfUnion (dnfMeetClause clause second) (dnfMeet rest second)))
      (LatticeTree.meetOp (LatticeTree.joinOp (meetOfClause clause) (combOfDnf rest)) (combOfDnf second))
    refine (dlCombDnfUnion (dnfMeetClause clause second) (dnfMeet rest second)).trans ?_
    refine (DistributiveLatticeTreeConv.joinCongr (dlCombDnfMeetClause clause second) ih).trans ?_
    exact (dlMeetJoinRightDistrib (meetOfClause clause) (combOfDnf rest) (combOfDnf second)).symm

/-- ★ **DNF join computes the join** — `combOfDnf (dnfJoin first second) ≈ join(combOfDnf first,
combOfDnf second)`.  `dnfJoin` is `dnfUnion`, so this is `dlCombDnfUnion`. -/
theorem dlCombDnfJoin (first second : List (List Nat)) :
    DistributiveLatticeTreeConv (combOfDnf (dnfJoin first second))
      (LatticeTree.joinOp (combOfDnf first) (combOfDnf second)) :=
  dlCombDnfUnion first second

/-! ## The reduction to canonical form and COMPLETENESS -/

/-- ★ **Normalization / reduction** — every tree is convertible to the join-of-meets comb of its own
minimal-DNF antichain: `tree ≈ combOfDnf (dnfOf tree)`.  Induction on the tree: `gen` / `topOp` / `botOp` are
the base combs (unit laws); `meetOp` normalizes both children (`meetCongr`) then rebuilds via `dlCombDnfMeet`;
`joinOp` likewise via `dlCombDnfJoin`.  This is the distributive-lattice analogue of the semilattice
`finiteSetTreeReducesToComb`, now carrying the two-operation DNF and the absorption-driven minimization. -/
theorem dlTreeReducesToDnfComb (tree : LatticeTree) :
    DistributiveLatticeTreeConv tree (combOfDnf (dnfOf tree)) := by
  induction tree with
  | gen colour =>
    show DistributiveLatticeTreeConv (LatticeTree.gen colour)
      (LatticeTree.joinOp (LatticeTree.meetOp (LatticeTree.gen colour) LatticeTree.topOp)
        LatticeTree.botOp)
    exact (DistributiveLatticeTreeConv.meetTop (LatticeTree.gen colour)).symm.trans
      (DistributiveLatticeTreeConv.joinBot
        (LatticeTree.meetOp (LatticeTree.gen colour) LatticeTree.topOp)).symm
  | topOp =>
    show DistributiveLatticeTreeConv LatticeTree.topOp
      (LatticeTree.joinOp LatticeTree.topOp LatticeTree.botOp)
    exact (DistributiveLatticeTreeConv.joinBot LatticeTree.topOp).symm
  | botOp => exact DistributiveLatticeTreeConv.refl _
  | meetOp left right ihLeft ihRight =>
    show DistributiveLatticeTreeConv (LatticeTree.meetOp left right)
      (combOfDnf (dnfMeet (dnfOf left) (dnfOf right)))
    exact (DistributiveLatticeTreeConv.meetCongr ihLeft ihRight).trans
      (dlCombDnfMeet (dnfOf left) (dnfOf right)).symm
  | joinOp left right ihLeft ihRight =>
    show DistributiveLatticeTreeConv (LatticeTree.joinOp left right)
      (combOfDnf (dnfJoin (dnfOf left) (dnfOf right)))
    exact (DistributiveLatticeTreeConv.joinCongr ihLeft ihRight).trans
      (dlCombDnfJoin (dnfOf left) (dnfOf right)).symm

/-- ★ **Completeness** — equal minimal-DNF antichains imply convertibility.  Both trees reduce to the comb of
their (equal) canonical DNF (`dlTreeReducesToDnfComb`), so they are convertible through that common normal
form.  This is the `⟸` half of the `Conv s t ↔ dnfOf s = dnfOf t` decision; the `⟹` half is the round-2
`distributiveLatticeTreeConv_sound` below.  Zero-axiom (only a plain `LatticeTree` equality transported into
`Conv`). -/
theorem distributiveLatticeTreeConv_complete {source target : LatticeTree}
    (dnfEq : dnfOf source = dnfOf target) :
    DistributiveLatticeTreeConv source target := by
  have sourceReduces : DistributiveLatticeTreeConv source (combOfDnf (dnfOf source)) :=
    dlTreeReducesToDnfComb source
  have targetReduces : DistributiveLatticeTreeConv target (combOfDnf (dnfOf target)) :=
    dlTreeReducesToDnfComb target
  have combEq : combOfDnf (dnfOf source) = combOfDnf (dnfOf target) := congrArg combOfDnf dnfEq
  exact DistributiveLatticeTreeConv.trans sourceReduces
    (combEq.symm ▸ DistributiveLatticeTreeConv.symm targetReduces)

/-! ## Completeness in action (convertibility decided by equal canonical DNF) -/

/-- ★ **The completeness decision in action (join commutativity)** — `join(g0, g1) ≈ join(g1, g0)` is derived
with NO explicit rewrite path: both trees have the same canonical DNF antichain `{ {0}, {1} }`
(`dnfOf` computes them equal by `rfl`), and completeness turns that structural equality into convertibility. -/
theorem distributiveLatticeCommViaCompleteness :
    DistributiveLatticeTreeConv
      (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1))
      (LatticeTree.joinOp (LatticeTree.gen 1) (LatticeTree.gen 0)) :=
  distributiveLatticeTreeConv_complete rfl

/-- ★ **The completeness decision in action (distributivity + reorder)** — the distinct-looking trees
`meet(g0, join(g1, g2))` and `join(meet(g1, g0), meet(g2, g0))` are convertible purely because their canonical
DNFs coincide (`{ {0,1}, {0,2} }`), decided by `rfl` on `dnfOf` through completeness — a genuinely
multi-step equivalence (distribute AND commute both meets) with no supplied derivation. -/
theorem distributiveLatticeReductionRoundtrips :
    DistributiveLatticeTreeConv
      (LatticeTree.meetOp (LatticeTree.gen 0)
        (LatticeTree.joinOp (LatticeTree.gen 1) (LatticeTree.gen 2)))
      (LatticeTree.joinOp
        (LatticeTree.meetOp (LatticeTree.gen 1) (LatticeTree.gen 0))
        (LatticeTree.meetOp (LatticeTree.gen 2) (LatticeTree.gen 0))) :=
  distributiveLatticeTreeConv_complete rfl

/-! ## ROUND 2 (SOUNDNESS) — STEP 1: the Boolean DNF evaluation and the comb bridge -/

/-- **Evaluate one clause under a Boolean environment** — the Boolean meet (`&&`) of the environment over the
clause's generators (`[] ↦ true`, the empty meet).  The list-level mirror of
`evalLatticeTree env ∘ meetOfClause`. -/
def dlEvalClause (env : Nat → Bool) : List Nat → Bool
  | [] => true
  | generator :: rest => env generator && dlEvalClause env rest

/-- **Evaluate a DNF under a Boolean environment** — the Boolean join (`||`) over the clauses of the Boolean
meet of each clause (`[] ↦ false`, the empty join).  The list-level mirror of
`evalLatticeTree env ∘ combOfDnf`. -/
def dlEvalDnf (env : Nat → Bool) : List (List Nat) → Bool
  | [] => false
  | clause :: rest => dlEvalClause env clause || dlEvalDnf env rest

/-- The clause comb evaluates to the clause's Boolean meet:
`evalLatticeTree env (meetOfClause clause) = dlEvalClause env clause`.  Structural induction. -/
theorem dlEvalMeetOfClause (env : Nat → Bool) : (clause : List Nat) →
    evalLatticeTree env (meetOfClause clause) = dlEvalClause env clause
  | [] => rfl
  | generator :: rest => by
      show (env generator && evalLatticeTree env (meetOfClause rest))
        = (env generator && dlEvalClause env rest)
      rw [dlEvalMeetOfClause env rest]

/-- The DNF comb evaluates to the DNF's Boolean join:
`evalLatticeTree env (combOfDnf dnf) = dlEvalDnf env dnf`.  Structural induction over
`dlEvalMeetOfClause`. -/
theorem dlEvalCombOfDnf (env : Nat → Bool) : (dnf : List (List Nat)) →
    evalLatticeTree env (combOfDnf dnf) = dlEvalDnf env dnf
  | [] => rfl
  | clause :: rest => by
      show (evalLatticeTree env (meetOfClause clause) || evalLatticeTree env (combOfDnf rest))
        = (dlEvalClause env clause || dlEvalDnf env rest)
      rw [dlEvalMeetOfClause env clause, dlEvalCombOfDnf env rest]

/-- ★ **Every tree evaluates through its canonical DNF** — `evalLatticeTree env tree = dlEvalDnf env
(dnfOf tree)`: compose the reduction `dlTreeReducesToDnfComb` with the evaluation soundness
`distributiveLatticeTreeConv_eval_sound` and the comb bridge `dlEvalCombOfDnf`.  Environments are only ever
APPLIED — no function extensionality anywhere. -/
theorem dlEvalViaDnf (env : Nat → Bool) (tree : LatticeTree) :
    evalLatticeTree env tree = dlEvalDnf env (dnfOf tree) :=
  (distributiveLatticeTreeConv_eval_sound (dlTreeReducesToDnfComb tree) env).trans
    (dlEvalCombOfDnf env (dnfOf tree))

/-- The **characteristic environment** of a clause — `true` exactly on the clause's generators.  These are
the finitely many evaluation points at which the uniqueness argument reads a canonical DNF's membership back
off its monotone Boolean function. -/
def dlCharacteristicEnv (clause : List Nat) : Nat → Bool :=
  fun generator => genMember generator clause

/-- **The clause-level characteristic bridge** — under `chi(larger)` a clause's Boolean meet computes exactly
the containment test: `dlEvalClause (chi larger) clause = clauseSubset clause larger`.  Unconditional (no
sortedness hypothesis): both sides scan the clause left to right. -/
theorem dlEvalClauseChar (larger : List Nat) : (clause : List Nat) →
    dlEvalClause (dlCharacteristicEnv larger) clause = clauseSubset clause larger
  | [] => rfl
  | head :: tail => by
      show (genMember head larger && dlEvalClause (dlCharacteristicEnv larger) tail)
        = clauseSubset (head :: tail) larger
      cases hMem : genMember head larger with
      | true =>
        rw [dlClauseSubsetConsMem head tail larger hMem]
        exact dlEvalClauseChar larger tail
      | false =>
        rw [dlClauseSubsetConsFalse head tail larger hMem]
        rfl

/-- ★ **The DNF-level characteristic bridge** — under `chi(candidate)` a DNF's Boolean join computes exactly
the absorption test: `dlEvalDnf (chi candidate) dnf = dnfHasSubsetOf candidate dnf`.  Unconditional. -/
theorem dlEvalDnfChar (candidate : List Nat) : (dnf : List (List Nat)) →
    dlEvalDnf (dlCharacteristicEnv candidate) dnf = dnfHasSubsetOf candidate dnf
  | [] => rfl
  | clause :: rest => by
      show (dlEvalClause (dlCharacteristicEnv candidate) clause
            || dlEvalDnf (dlCharacteristicEnv candidate) rest)
        = dnfHasSubsetOf candidate (clause :: rest)
      rw [dlEvalClauseChar candidate clause]
      cases hSub : clauseSubset clause candidate with
      | true =>
        rw [dlHasSubsetConsTrue candidate clause rest hSub]
        rfl
      | false =>
        rw [dlHasSubsetConsFalse candidate clause rest hSub]
        exact dlEvalDnfChar candidate rest

/-! ## ROUND 2 — STEP 2: structural clause / DNF equality scans (the membership kit) -/

/-- Reflexivity of the core `Nat.beq` — a self-contained structural proof (no library lemma). -/
theorem dlNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => dlNatBeqRefl predecessor

/-- **Structural clause equality** — `List Nat` Boolean equality via `Nat.beq`, the antichain-membership
comparator. -/
def dlClauseBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | headFirst :: tailFirst, headSecond :: tailSecond =>
      match Nat.beq headFirst headSecond with
      | true => dlClauseBeq tailFirst tailSecond
      | false => false

/-- `dlClauseBeq` cons equation (EQUAL heads): defer to the tails. -/
theorem dlClauseBeqConsTrue (headFirst headSecond : Nat) (tailFirst tailSecond : List Nat)
    (h : Nat.beq headFirst headSecond = true) :
    dlClauseBeq (headFirst :: tailFirst) (headSecond :: tailSecond)
      = dlClauseBeq tailFirst tailSecond := by
  show (match Nat.beq headFirst headSecond with
        | true => dlClauseBeq tailFirst tailSecond
        | false => false) = dlClauseBeq tailFirst tailSecond
  rw [h]

/-- `dlClauseBeq` cons equation (DISTINCT heads): refuted. -/
theorem dlClauseBeqConsFalse (headFirst headSecond : Nat) (tailFirst tailSecond : List Nat)
    (h : Nat.beq headFirst headSecond = false) :
    dlClauseBeq (headFirst :: tailFirst) (headSecond :: tailSecond) = false := by
  show (match Nat.beq headFirst headSecond with
        | true => dlClauseBeq tailFirst tailSecond
        | false => false) = false
  rw [h]

/-- `dlClauseBeq` is reflexive. -/
theorem dlClauseBeqRefl : (clause : List Nat) → dlClauseBeq clause clause = true
  | [] => rfl
  | head :: tail => by
      rw [dlClauseBeqConsTrue head head tail tail (dlNatBeqRefl head)]
      exact dlClauseBeqRefl tail

/-- `dlClauseBeq` decides equality: `true` forces the clauses equal.  Structural double recursion via
`dlNatBeqEq`. -/
theorem dlClauseBeqEq : (first second : List Nat) → dlClauseBeq first second = true → first = second := by
  intro first
  induction first with
  | nil =>
    intro second h
    cases second with
    | nil => rfl
    | cons headSecond tailSecond => exact Bool.noConfusion h
  | cons headFirst tailFirst ih =>
    intro second h
    cases second with
    | nil => exact Bool.noConfusion h
    | cons headSecond tailSecond =>
      cases hHead : Nat.beq headFirst headSecond with
      | false =>
        rw [dlClauseBeqConsFalse headFirst headSecond tailFirst tailSecond hHead] at h
        exact Bool.noConfusion h
      | true =>
        rw [dlClauseBeqConsTrue headFirst headSecond tailFirst tailSecond hHead] at h
        rw [dlNatBeqEq headFirst headSecond hHead, ih tailSecond h]

/-- **DNF clause membership** — does the DNF contain `needle` as one of its clauses (structural
`dlClauseBeq` scan)? -/
def dlDnfHasClause (needle : List Nat) : List (List Nat) → Bool
  | [] => false
  | clause :: rest =>
      match dlClauseBeq clause needle with
      | true => true
      | false => dlDnfHasClause needle rest

/-- `dlDnfHasClause` cons equation (HIT): a beq-equal head witnesses membership. -/
theorem dlDnfHasClauseConsTrue (needle clause : List Nat) (rest : List (List Nat))
    (h : dlClauseBeq clause needle = true) : dlDnfHasClause needle (clause :: rest) = true := by
  show (match dlClauseBeq clause needle with
        | true => true
        | false => dlDnfHasClause needle rest) = true
  rw [h]

/-- `dlDnfHasClause` cons equation (MISS): a beq-distinct head defers to the rest. -/
theorem dlDnfHasClauseConsFalse (needle clause : List Nat) (rest : List (List Nat))
    (h : dlClauseBeq clause needle = false) :
    dlDnfHasClause needle (clause :: rest) = dlDnfHasClause needle rest := by
  show (match dlClauseBeq clause needle with
        | true => true
        | false => dlDnfHasClause needle rest) = dlDnfHasClause needle rest
  rw [h]

/-- The head clause is a member. -/
theorem dlDnfHasClauseHead (clause : List Nat) (rest : List (List Nat)) :
    dlDnfHasClause clause (clause :: rest) = true :=
  dlDnfHasClauseConsTrue clause clause rest (dlClauseBeqRefl clause)

/-- Membership in the tail weakens to membership in the cons. -/
theorem dlDnfHasClauseConsWeaken (needle clause : List Nat) (rest : List (List Nat))
    (h : dlDnfHasClause needle rest = true) : dlDnfHasClause needle (clause :: rest) = true := by
  cases hBeq : dlClauseBeq clause needle with
  | true => exact dlDnfHasClauseConsTrue needle clause rest hBeq
  | false => rw [dlDnfHasClauseConsFalse needle clause rest hBeq]; exact h

/-- The head generator is a member of its own cons. -/
theorem dlGenMemberHead (head : Nat) (tail : List Nat) : genMember head (head :: tail) = true := by
  show (match Nat.beq head head with
        | true => true
        | false => genMember head tail) = true
  rw [dlNatBeqRefl head]

/-- Generator membership in the tail weakens to membership in the cons. -/
theorem dlGenMemberConsWeaken (target head : Nat) (tail : List Nat)
    (h : genMember target tail = true) : genMember target (head :: tail) = true := by
  cases hBeq : Nat.beq head target with
  | true =>
    show (match Nat.beq head target with
          | true => true
          | false => genMember target tail) = true
    rw [hBeq]
  | false => rw [dlGenMemberConsFalse target head tail hBeq]; exact h

/-! ## ROUND 2 — STEP 3: the clause-containment kit (intro / elim / erase) -/

/-- **Pointwise introduction of `clauseSubset`** — if every generator of `smaller` is a member of `larger`
then `clauseSubset smaller larger = true`. -/
theorem dlClauseSubsetIntro : (smaller : List Nat) → (larger : List Nat) →
    (∀ generator : Nat, genMember generator smaller = true → genMember generator larger = true) →
    clauseSubset smaller larger = true := by
  intro smaller
  induction smaller with
  | nil => intro larger hPoint; rfl
  | cons head tail ih =>
    intro larger hPoint
    have hHead : genMember head larger = true := hPoint head (dlGenMemberHead head tail)
    rw [dlClauseSubsetConsMem head tail larger hHead]
    exact ih larger (fun generator hMem => hPoint generator (dlGenMemberConsWeaken generator head tail hMem))

/-- **Pointwise elimination of `clauseSubset`** — a containment transports each generator membership. -/
theorem dlClauseSubsetElim : (smaller : List Nat) → (larger : List Nat) →
    clauseSubset smaller larger = true → (generator : Nat) → genMember generator smaller = true →
    genMember generator larger = true := by
  intro smaller
  induction smaller with
  | nil => intro larger hSub generator hMem; exact Bool.noConfusion hMem
  | cons head tail ih =>
    intro larger hSub generator hMem
    cases hHeadMem : genMember head larger with
    | false =>
      rw [dlClauseSubsetConsFalse head tail larger hHeadMem] at hSub
      exact Bool.noConfusion hSub
    | true =>
      rw [dlClauseSubsetConsMem head tail larger hHeadMem] at hSub
      cases hBeq : Nat.beq head generator with
      | true => rw [← dlNatBeqEq head generator hBeq]; exact hHeadMem
      | false =>
        rw [dlGenMemberConsFalse generator head tail hBeq] at hMem
        exact ih larger hSub generator hMem

/-- `clauseSubset` is reflexive. -/
theorem dlClauseSubsetRefl (clause : List Nat) : clauseSubset clause clause = true :=
  dlClauseSubsetIntro clause clause (fun _ hMem => hMem)

/-- `clauseSubset` is transitive. -/
theorem dlClauseSubsetTrans (lower middle upper : List Nat)
    (hLM : clauseSubset lower middle = true) (hMU : clauseSubset middle upper = true) :
    clauseSubset lower upper = true :=
  dlClauseSubsetIntro lower upper (fun generator hMem =>
    dlClauseSubsetElim middle upper hMU generator (dlClauseSubsetElim lower middle hLM generator hMem))

/-- **A failed containment yields a missing generator** — `clauseSubset smaller larger = false` produces a
generator of `smaller` absent from `larger`. -/
theorem dlClauseSubsetFalseWitness : (smaller : List Nat) → (larger : List Nat) →
    clauseSubset smaller larger = false →
    ∃ generator : Nat, genMember generator smaller = true ∧ genMember generator larger = false := by
  intro smaller
  induction smaller with
  | nil => intro larger hFalse; exact Bool.noConfusion hFalse
  | cons head tail ih =>
    intro larger hFalse
    cases hHeadMem : genMember head larger with
    | false => exact ⟨head, dlGenMemberHead head tail, hHeadMem⟩
    | true =>
      rw [dlClauseSubsetConsMem head tail larger hHeadMem] at hFalse
      have ⟨generator, hMem, hMiss⟩ := ih larger hFalse
      exact ⟨generator, dlGenMemberConsWeaken generator head tail hMem, hMiss⟩

/-- **Erase one generator from a clause** — the `Nat.beq` filter dropping every copy of `target`.  Its
characteristic environment is the minimality probe of the prime-implicant test. -/
def dlEraseGenerator (target : Nat) : List Nat → List Nat
  | [] => []
  | head :: rest =>
      match Nat.beq head target with
      | true => dlEraseGenerator target rest
      | false => head :: dlEraseGenerator target rest

/-- `dlEraseGenerator` cons equation (DROP): the target head is removed. -/
theorem dlEraseGeneratorConsDrop (target head : Nat) (rest : List Nat)
    (h : Nat.beq head target = true) :
    dlEraseGenerator target (head :: rest) = dlEraseGenerator target rest := by
  show (match Nat.beq head target with
        | true => dlEraseGenerator target rest
        | false => head :: dlEraseGenerator target rest) = dlEraseGenerator target rest
  rw [h]

/-- `dlEraseGenerator` cons equation (KEEP): a non-target head survives. -/
theorem dlEraseGeneratorConsKeep (target head : Nat) (rest : List Nat)
    (h : Nat.beq head target = false) :
    dlEraseGenerator target (head :: rest) = head :: dlEraseGenerator target rest := by
  show (match Nat.beq head target with
        | true => dlEraseGenerator target rest
        | false => head :: dlEraseGenerator target rest) = head :: dlEraseGenerator target rest
  rw [h]

/-- Erasing a generator removes it: `genMember target (dlEraseGenerator target clause) = false`. -/
theorem dlGenMemberEraseSelf (target : Nat) : (clause : List Nat) →
    genMember target (dlEraseGenerator target clause) = false := by
  intro clause
  induction clause with
  | nil => rfl
  | cons head rest ih =>
    cases hBeq : Nat.beq head target with
    | true => rw [dlEraseGeneratorConsDrop target head rest hBeq]; exact ih
    | false =>
      rw [dlEraseGeneratorConsKeep target head rest hBeq,
          dlGenMemberConsFalse target head (dlEraseGenerator target rest) hBeq]
      exact ih

/-- Erasing a DIFFERENT generator preserves membership. -/
theorem dlGenMemberEraseOther (generator target : Nat) (hNe : Nat.beq generator target = false) :
    (clause : List Nat) → genMember generator clause = true →
    genMember generator (dlEraseGenerator target clause) = true := by
  intro clause
  induction clause with
  | nil => intro hMem; exact Bool.noConfusion hMem
  | cons head rest ih =>
    intro hMem
    cases hHeadGen : Nat.beq head generator with
    | true =>
      have hHeadTarget : Nat.beq head target = false := by
        rw [dlNatBeqEq head generator hHeadGen]; exact hNe
      rw [dlEraseGeneratorConsKeep target head rest hHeadTarget]
      show (match Nat.beq head generator with
            | true => true
            | false => genMember generator (dlEraseGenerator target rest)) = true
      rw [hHeadGen]
    | false =>
      rw [dlGenMemberConsFalse generator head rest hHeadGen] at hMem
      cases hHeadTarget : Nat.beq head target with
      | true => rw [dlEraseGeneratorConsDrop target head rest hHeadTarget]; exact ih hMem
      | false =>
        rw [dlEraseGeneratorConsKeep target head rest hHeadTarget,
            dlGenMemberConsFalse generator head (dlEraseGenerator target rest) hHeadGen]
        exact ih hMem

/-- Membership in the erased clause reflects back to the original clause. -/
theorem dlGenMemberEraseElim (generator target : Nat) : (clause : List Nat) →
    genMember generator (dlEraseGenerator target clause) = true →
    genMember generator clause = true := by
  intro clause
  induction clause with
  | nil => intro hMem; exact Bool.noConfusion hMem
  | cons head rest ih =>
    intro hMem
    cases hHeadTarget : Nat.beq head target with
    | true =>
      rw [dlEraseGeneratorConsDrop target head rest hHeadTarget] at hMem
      exact dlGenMemberConsWeaken generator head rest (ih hMem)
    | false =>
      rw [dlEraseGeneratorConsKeep target head rest hHeadTarget] at hMem
      cases hHeadGen : Nat.beq head generator with
      | true =>
        show (match Nat.beq head generator with
              | true => true
              | false => genMember generator rest) = true
        rw [hHeadGen]
      | false =>
        rw [dlGenMemberConsFalse generator head (dlEraseGenerator target rest) hHeadGen] at hMem
        rw [dlGenMemberConsFalse generator head rest hHeadGen]
        exact ih hMem

/-- The erased clause is contained in the original clause. -/
theorem dlEraseSubset (target : Nat) (clause : List Nat) :
    clauseSubset (dlEraseGenerator target clause) clause = true :=
  dlClauseSubsetIntro (dlEraseGenerator target clause) clause
    (fun generator hMem => dlGenMemberEraseElim generator target clause hMem)

/-- **Containment survives erasing a generator the smaller clause misses** — if `smaller ⊆ larger` and
`target ∉ smaller` then `smaller ⊆ larger \ {target}`. -/
theorem dlClauseSubsetEraseIntro (smaller larger : List Nat) (target : Nat)
    (hSub : clauseSubset smaller larger = true) (hMiss : genMember target smaller = false) :
    clauseSubset smaller (dlEraseGenerator target larger) = true :=
  dlClauseSubsetIntro smaller (dlEraseGenerator target larger) (fun generator hMem => by
    have hInLarger : genMember generator larger = true :=
      dlClauseSubsetElim smaller larger hSub generator hMem
    cases hBeq : Nat.beq generator target with
    | true =>
      rw [dlNatBeqEq generator target hBeq] at hMem
      rw [hMem] at hMiss
      exact Bool.noConfusion hMiss
    | false => exact dlGenMemberEraseOther generator target hBeq larger hInLarger)

/-! ## ROUND 2 — STEP 4: the strict clause order kit (transitivity / irreflexivity / asymmetry) -/

/-- `clauseLess` equation (STRICTLY LONGER first): a first clause of strictly larger length is not below. -/
theorem dlClauseLessGtFalse (first second : List Nat)
    (h : natBle (clauseLength first) (clauseLength second) = false) :
    clauseLess first second = false := by
  show (match natBle (clauseLength first) (clauseLength second) with
        | false => false
        | true =>
            match natBle (clauseLength second) (clauseLength first) with
            | false => true
            | true => clauseLexLess first second) = false
  rw [h]

/-- **Strict-less transitivity in the `natBle`-false encoding** — `lower < middle` and `middle < upper`
give `lower < upper` (where `x < y` is `natBle y x = false`). -/
theorem dlNatLtTrans (lower middle upper : Nat)
    (hLM : natBle middle lower = false) (hMU : natBle upper middle = false) :
    natBle upper lower = false := by
  cases hUL : natBle upper lower with
  | false => rfl
  | true =>
    have hLMTrue : natBle lower middle = true := natBleTotal middle lower hLM
    have hUM : natBle upper middle = true := natBleTrans upper lower middle hUL hLMTrue
    rw [hUM] at hMU
    exact Bool.noConfusion hMU

/-- `clauseLexLess` is irreflexive. -/
theorem dlClauseLexIrrefl : (clause : List Nat) → clauseLexLess clause clause = false
  | [] => rfl
  | head :: tail => by
      rw [dlClauseLexEqStep head head tail tail (natBleRefl head) (natBleRefl head)]
      exact dlClauseLexIrrefl tail

/-- `clauseLess` is irreflexive. -/
theorem dlClauseLessIrrefl (clause : List Nat) : clauseLess clause clause = false := by
  rw [dlClauseLessEqStep clause clause (natBleRefl (clauseLength clause)) (natBleRefl (clauseLength clause))]
  exact dlClauseLexIrrefl clause

/-- `clauseLexLess` is asymmetric. -/
theorem dlClauseLexAsymm : (first : List Nat) → (second : List Nat) →
    clauseLexLess first second = true → clauseLexLess second first = false := by
  intro first
  induction first with
  | nil =>
    intro second h
    cases second with
    | nil => exact Bool.noConfusion h
    | cons headSecond tailSecond => rfl
  | cons headFirst tailFirst ih =>
    intro second h
    cases second with
    | nil => exact Bool.noConfusion h
    | cons headSecond tailSecond =>
      cases hFS : natBle headFirst headSecond with
      | false =>
        rw [dlClauseLexGt headFirst headSecond tailFirst tailSecond hFS] at h
        exact Bool.noConfusion h
      | true =>
        cases hSF : natBle headSecond headFirst with
        | false => exact dlClauseLexGt headSecond headFirst tailSecond tailFirst hSF
        | true =>
          rw [dlClauseLexEqStep headFirst headSecond tailFirst tailSecond hFS hSF] at h
          rw [dlClauseLexEqStep headSecond headFirst tailSecond tailFirst hSF hFS]
          exact ih tailSecond h

/-- `clauseLess` is asymmetric — used to refute a head clash in the sorted-extensionality argument. -/
theorem dlClauseLessAsymm (first second : List Nat)
    (h : clauseLess first second = true) : clauseLess second first = false := by
  cases hFS : natBle (clauseLength first) (clauseLength second) with
  | false =>
    rw [dlClauseLessGtFalse first second hFS] at h
    exact Bool.noConfusion h
  | true =>
    cases hSF : natBle (clauseLength second) (clauseLength first) with
    | false => exact dlClauseLessGtFalse second first hSF
    | true =>
      rw [dlClauseLessEqStep first second hFS hSF] at h
      rw [dlClauseLessEqStep second first hSF hFS]
      exact dlClauseLexAsymm first second h

/-- `clauseLexLess` is transitive.  Simultaneous descent on the three clauses; the head comparisons split
LESS / EQUAL / GREATER through `natBleTrans` / `natBleAntisymm` / `natBleTotal`. -/
theorem dlClauseLexTrans : (first : List Nat) → (second third : List Nat) →
    clauseLexLess first second = true → clauseLexLess second third = true →
    clauseLexLess first third = true := by
  intro first
  induction first with
  | nil =>
    intro second third h1 h2
    cases second with
    | nil => exact Bool.noConfusion h1
    | cons headSecond tailSecond =>
      cases third with
      | nil => exact Bool.noConfusion h2
      | cons headThird tailThird => rfl
  | cons headFirst tailFirst ih =>
    intro second third h1 h2
    cases second with
    | nil => exact Bool.noConfusion h1
    | cons headSecond tailSecond =>
      cases third with
      | nil => exact Bool.noConfusion h2
      | cons headThird tailThird =>
        cases hFS : natBle headFirst headSecond with
        | false =>
          rw [dlClauseLexGt headFirst headSecond tailFirst tailSecond hFS] at h1
          exact Bool.noConfusion h1
        | true =>
          cases hST : natBle headSecond headThird with
          | false =>
            rw [dlClauseLexGt headSecond headThird tailSecond tailThird hST] at h2
            exact Bool.noConfusion h2
          | true =>
            have hFT : natBle headFirst headThird = true :=
              natBleTrans headFirst headSecond headThird hFS hST
            cases hSF : natBle headSecond headFirst with
            | false =>
              have hTF : natBle headThird headFirst = false := by
                cases hTFprobe : natBle headThird headFirst with
                | false => rfl
                | true =>
                  have hSFcontra : natBle headSecond headFirst = true :=
                    natBleTrans headSecond headThird headFirst hST hTFprobe
                  rw [hSFcontra] at hSF
                  exact Bool.noConfusion hSF
              exact dlClauseLexLt headFirst headThird tailFirst tailThird hFT hTF
            | true =>
              have hHeadFS : headFirst = headSecond := natBleAntisymm headFirst headSecond hFS hSF
              rw [dlClauseLexEqStep headFirst headSecond tailFirst tailSecond hFS hSF] at h1
              cases hTS : natBle headThird headSecond with
              | false =>
                have hTF : natBle headThird headFirst = false := by
                  rw [hHeadFS]; exact hTS
                exact dlClauseLexLt headFirst headThird tailFirst tailThird hFT hTF
              | true =>
                have hHeadST : headSecond = headThird := natBleAntisymm headSecond headThird hST hTS
                rw [dlClauseLexEqStep headSecond headThird tailSecond tailThird hST hTS] at h2
                have hTF : natBle headThird headFirst = true := by
                  rw [hHeadFS, hHeadST]; exact natBleRefl headThird
                rw [dlClauseLexEqStep headFirst headThird tailFirst tailThird hFT hTF]
                exact ih tailSecond tailThird h1 h2

/-- ★ `clauseLess` is transitive — length comparison first (through `natBleTrans`), the equal-length tie
resolved by `dlClauseLexTrans`.  The engine of the sorted-DNF invariant. -/
theorem dlClauseLessTrans (first second third : List Nat)
    (h1 : clauseLess first second = true) (h2 : clauseLess second third = true) :
    clauseLess first third = true := by
  cases hFS : natBle (clauseLength first) (clauseLength second) with
  | false =>
    rw [dlClauseLessGtFalse first second hFS] at h1
    exact Bool.noConfusion h1
  | true =>
    cases hST : natBle (clauseLength second) (clauseLength third) with
    | false =>
      rw [dlClauseLessGtFalse second third hST] at h2
      exact Bool.noConfusion h2
    | true =>
      have hFT : natBle (clauseLength first) (clauseLength third) = true :=
        natBleTrans (clauseLength first) (clauseLength second) (clauseLength third) hFS hST
      cases hSF : natBle (clauseLength second) (clauseLength first) with
      | false =>
        have hTF : natBle (clauseLength third) (clauseLength first) = false := by
          cases hTFprobe : natBle (clauseLength third) (clauseLength first) with
          | false => rfl
          | true =>
            have hSFcontra : natBle (clauseLength second) (clauseLength first) = true :=
              natBleTrans (clauseLength second) (clauseLength third) (clauseLength first) hST hTFprobe
            rw [hSFcontra] at hSF
            exact Bool.noConfusion hSF
        exact dlClauseLessLt first third hFT hTF
      | true =>
        have hLenFS : clauseLength first = clauseLength second :=
          natBleAntisymm (clauseLength first) (clauseLength second) hFS hSF
        rw [dlClauseLessEqStep first second hFS hSF] at h1
        cases hTS : natBle (clauseLength third) (clauseLength second) with
        | false =>
          have hTF : natBle (clauseLength third) (clauseLength first) = false := by
            rw [hLenFS]; exact hTS
          exact dlClauseLessLt first third hFT hTF
        | true =>
          rw [dlClauseLessEqStep second third hST hTS] at h2
          have hTF : natBle (clauseLength third) (clauseLength first) = true := by
            rw [hLenFS]; exact hTS
          rw [dlClauseLessEqStep first third hFT hTF]
          exact dlClauseLexTrans first second third h1 h2

/-! ## ROUND 2 — STEP 5a: clause-level strict sortedness (sorted-distinct generator lists) -/

/-- Is `bound` STRICTLY below every generator of the clause?  (`bound < head` is `natBle head bound =
false`.)  The hereditary head condition of a sorted-distinct clause. -/
def dlIsGenBelowClause (bound : Nat) : List Nat → Bool
  | [] => true
  | head :: rest =>
      match natBle head bound with
      | true => false
      | false => dlIsGenBelowClause bound rest

/-- `dlIsGenBelowClause` cons equation (NOT BELOW): a head at or under the bound refutes. -/
theorem dlGenBelowClauseConsLe (bound head : Nat) (rest : List Nat)
    (h : natBle head bound = true) : dlIsGenBelowClause bound (head :: rest) = false := by
  show (match natBle head bound with
        | true => false
        | false => dlIsGenBelowClause bound rest) = false
  rw [h]

/-- `dlIsGenBelowClause` cons equation (BELOW): a head strictly above the bound defers to the rest. -/
theorem dlGenBelowClauseConsGt (bound head : Nat) (rest : List Nat)
    (h : natBle head bound = false) :
    dlIsGenBelowClause bound (head :: rest) = dlIsGenBelowClause bound rest := by
  show (match natBle head bound with
        | true => false
        | false => dlIsGenBelowClause bound rest) = dlIsGenBelowClause bound rest
  rw [h]

/-- `dlIsGenBelowClause` cons introduction. -/
theorem dlGenBelowClauseConsIntro (bound head : Nat) (rest : List Nat)
    (hHead : natBle head bound = false) (hRest : dlIsGenBelowClause bound rest = true) :
    dlIsGenBelowClause bound (head :: rest) = true := by
  rw [dlGenBelowClauseConsGt bound head rest hHead]
  exact hRest

/-- A lower bound transports below-clause status downward: `lower < upper` and `upper` below the clause
give `lower` below the clause. -/
theorem dlGenBelowClauseTrans (lower upper : Nat) (hLU : natBle upper lower = false) :
    (clause : List Nat) → dlIsGenBelowClause upper clause = true →
    dlIsGenBelowClause lower clause = true := by
  intro clause
  induction clause with
  | nil => intro hAbove; rfl
  | cons head rest ih =>
    intro hAbove
    cases hHU : natBle head upper with
    | true =>
      rw [dlGenBelowClauseConsLe upper head rest hHU] at hAbove
      exact Bool.noConfusion hAbove
    | false =>
      rw [dlGenBelowClauseConsGt upper head rest hHU] at hAbove
      exact dlGenBelowClauseConsIntro lower head rest (dlNatLtTrans lower upper head hLU hHU) (ih hAbove)

/-- A strict lower bound survives a sorted-set insert of a strictly larger value. -/
theorem dlGenBelowClauseInsert (bound value : Nat) (hBV : natBle value bound = false) :
    (clause : List Nat) → dlIsGenBelowClause bound clause = true →
    dlIsGenBelowClause bound (insertSortedSet value clause) = true := by
  intro clause
  induction clause with
  | nil =>
    intro hBelow
    show dlIsGenBelowClause bound [value] = true
    exact dlGenBelowClauseConsIntro bound value [] hBV rfl
  | cons head rest ih =>
    intro hBelow
    cases hHead : natBle head bound with
    | true =>
      rw [dlGenBelowClauseConsLe bound head rest hHead] at hBelow
      exact Bool.noConfusion hBelow
    | false =>
      rw [dlGenBelowClauseConsGt bound head rest hHead] at hBelow
      cases hVH : natBle value head with
      | true =>
        cases hHV : natBle head value with
        | true =>
          rw [insertSortedSetEq value head rest hVH hHV]
          exact dlGenBelowClauseConsIntro bound head rest hHead hBelow
        | false =>
          rw [insertSortedSetLt value head rest hVH hHV]
          exact dlGenBelowClauseConsIntro bound value (head :: rest) hBV
            (dlGenBelowClauseConsIntro bound head rest hHead hBelow)
      | false =>
        rw [insertSortedSetGt value head rest hVH]
        exact dlGenBelowClauseConsIntro bound head (insertSortedSet value rest) hHead (ih hBelow)

/-- Is the clause a STRICTLY sorted generator list (sorted and duplicate-free)?  The canonical clause
invariant maintained by `insertSortedSet`. -/
def dlIsSortedClause : List Nat → Bool
  | [] => true
  | head :: rest =>
      match dlIsGenBelowClause head rest with
      | true => dlIsSortedClause rest
      | false => false

/-- `dlIsSortedClause` cons equation (HEAD BELOW): defer to the rest. -/
theorem dlSortedClauseConsTrue (head : Nat) (rest : List Nat)
    (h : dlIsGenBelowClause head rest = true) :
    dlIsSortedClause (head :: rest) = dlIsSortedClause rest := by
  show (match dlIsGenBelowClause head rest with
        | true => dlIsSortedClause rest
        | false => false) = dlIsSortedClause rest
  rw [h]

/-- `dlIsSortedClause` cons equation (HEAD NOT BELOW): refuted. -/
theorem dlSortedClauseConsFalse (head : Nat) (rest : List Nat)
    (h : dlIsGenBelowClause head rest = false) : dlIsSortedClause (head :: rest) = false := by
  show (match dlIsGenBelowClause head rest with
        | true => dlIsSortedClause rest
        | false => false) = false
  rw [h]

/-- `dlIsSortedClause` cons introduction. -/
theorem dlSortedClauseConsIntro (head : Nat) (rest : List Nat)
    (hBelow : dlIsGenBelowClause head rest = true) (hRest : dlIsSortedClause rest = true) :
    dlIsSortedClause (head :: rest) = true := by
  rw [dlSortedClauseConsTrue head rest hBelow]
  exact hRest

/-- `dlIsSortedClause` cons elimination — both components of the invariant. -/
theorem dlSortedClauseConsElim (head : Nat) (rest : List Nat)
    (hSorted : dlIsSortedClause (head :: rest) = true) :
    dlIsGenBelowClause head rest = true ∧ dlIsSortedClause rest = true := by
  cases hBelow : dlIsGenBelowClause head rest with
  | false =>
    rw [dlSortedClauseConsFalse head rest hBelow] at hSorted
    exact Bool.noConfusion hSorted
  | true =>
    rw [dlSortedClauseConsTrue head rest hBelow] at hSorted
    exact ⟨rfl, hSorted⟩

/-- ★ `insertSortedSet` preserves clause sortedness. -/
theorem dlSortedClauseInsert (value : Nat) : (clause : List Nat) →
    dlIsSortedClause clause = true → dlIsSortedClause (insertSortedSet value clause) = true := by
  intro clause
  induction clause with
  | nil =>
    intro hSorted
    show dlIsSortedClause [value] = true
    exact dlSortedClauseConsIntro value [] rfl rfl
  | cons head rest ih =>
    intro hSorted
    have hParts := dlSortedClauseConsElim head rest hSorted
    cases hVH : natBle value head with
    | true =>
      cases hHV : natBle head value with
      | true =>
        rw [insertSortedSetEq value head rest hVH hHV]
        exact hSorted
      | false =>
        rw [insertSortedSetLt value head rest hVH hHV]
        exact dlSortedClauseConsIntro value (head :: rest)
          (dlGenBelowClauseConsIntro value head rest hHV
            (dlGenBelowClauseTrans value head hHV rest hParts.left))
          hSorted
    | false =>
      rw [insertSortedSetGt value head rest hVH]
      exact dlSortedClauseConsIntro head (insertSortedSet value rest)
        (dlGenBelowClauseInsert head value hVH rest hParts.left)
        (ih hParts.right)

/-- ★ `insertManySet` preserves clause sortedness of the accumulator (the inserted generators may arrive in
any order). -/
theorem dlSortedClauseInsertMany : (values : List Nat) → (acc : List Nat) →
    dlIsSortedClause acc = true → dlIsSortedClause (insertManySet values acc) = true := by
  intro values
  induction values with
  | nil => intro acc hSorted; exact hSorted
  | cons head tail ih =>
    intro acc hSorted
    show dlIsSortedClause (insertSortedSet head (insertManySet tail acc)) = true
    exact dlSortedClauseInsert head (insertManySet tail acc) (ih acc hSorted)

/-- In a clause with a strict head bound, every member is strictly above the bound. -/
theorem dlSortedHeadBelow (bound : Nat) : (tail : List Nat) →
    dlIsGenBelowClause bound tail = true → (generator : Nat) → genMember generator tail = true →
    natBle generator bound = false := by
  intro tail
  induction tail with
  | nil => intro hBelow generator hMem; exact Bool.noConfusion hMem
  | cons head rest ih =>
    intro hBelow generator hMem
    cases hHB : natBle head bound with
    | true =>
      rw [dlGenBelowClauseConsLe bound head rest hHB] at hBelow
      exact Bool.noConfusion hBelow
    | false =>
      rw [dlGenBelowClauseConsGt bound head rest hHB] at hBelow
      cases hBeq : Nat.beq head generator with
      | true => rw [← dlNatBeqEq head generator hBeq]; exact hHB
      | false =>
        rw [dlGenMemberConsFalse generator head rest hBeq] at hMem
        exact ih hBelow generator hMem

/-- ★ **Antisymmetry of clause containment on sorted-distinct clauses** — two strictly sorted clauses each
contained in the other are EQUAL as lists.  Double descent; the heads are forced equal (each is a member of
the other clause, and a sorted head is the strict minimum), then the tails are mutually contained because
the shared head cannot recur in either tail. -/
theorem dlClauseSubsetAntisymm : (first : List Nat) → (second : List Nat) →
    dlIsSortedClause first = true → dlIsSortedClause second = true →
    clauseSubset first second = true → clauseSubset second first = true → first = second := by
  intro first
  induction first with
  | nil =>
    intro second hSortedFirst hSortedSecond hFS hSF
    cases second with
    | nil => rfl
    | cons headSecond tailSecond =>
      rw [dlClauseSubsetConsFalse headSecond tailSecond [] rfl] at hSF
      exact Bool.noConfusion hSF
  | cons headFirst tailFirst ih =>
    intro second hSortedFirst hSortedSecond hFS hSF
    cases second with
    | nil =>
      rw [dlClauseSubsetConsFalse headFirst tailFirst [] rfl] at hFS
      exact Bool.noConfusion hFS
    | cons headSecond tailSecond =>
      have hPartsFirst := dlSortedClauseConsElim headFirst tailFirst hSortedFirst
      have hPartsSecond := dlSortedClauseConsElim headSecond tailSecond hSortedSecond
      cases hMemFirst : genMember headFirst (headSecond :: tailSecond) with
      | false =>
        rw [dlClauseSubsetConsFalse headFirst tailFirst (headSecond :: tailSecond) hMemFirst] at hFS
        exact Bool.noConfusion hFS
      | true =>
        rw [dlClauseSubsetConsMem headFirst tailFirst (headSecond :: tailSecond) hMemFirst] at hFS
        cases hMemSecond : genMember headSecond (headFirst :: tailFirst) with
        | false =>
          rw [dlClauseSubsetConsFalse headSecond tailSecond (headFirst :: tailFirst) hMemSecond] at hSF
          exact Bool.noConfusion hSF
        | true =>
          rw [dlClauseSubsetConsMem headSecond tailSecond (headFirst :: tailFirst) hMemSecond] at hSF
          have hHeadEq : headFirst = headSecond := by
            cases hBeqSF : Nat.beq headSecond headFirst with
            | true => exact (dlNatBeqEq headSecond headFirst hBeqSF).symm
            | false =>
              rw [dlGenMemberConsFalse headFirst headSecond tailSecond hBeqSF] at hMemFirst
              have hFbelowS : natBle headFirst headSecond = false :=
                dlSortedHeadBelow headSecond tailSecond hPartsSecond.left headFirst hMemFirst
              cases hBeqFS : Nat.beq headFirst headSecond with
              | true => exact dlNatBeqEq headFirst headSecond hBeqFS
              | false =>
                rw [dlGenMemberConsFalse headSecond headFirst tailFirst hBeqFS] at hMemSecond
                have hSbelowF : natBle headSecond headFirst = false :=
                  dlSortedHeadBelow headFirst tailFirst hPartsFirst.left headSecond hMemSecond
                have hTotal : natBle headSecond headFirst = true :=
                  natBleTotal headFirst headSecond hFbelowS
                rw [hTotal] at hSbelowF
                exact Bool.noConfusion hSbelowF
          subst hHeadEq
          have hTailFS : clauseSubset tailFirst tailSecond = true := by
            refine dlClauseSubsetIntro tailFirst tailSecond (fun generator hMem => ?_)
            have hInSecond : genMember generator (headFirst :: tailSecond) = true :=
              dlClauseSubsetElim tailFirst (headFirst :: tailSecond) hFS generator hMem
            cases hBeqHG : Nat.beq headFirst generator with
            | true =>
              have hGenBelow : natBle generator headFirst = false :=
                dlSortedHeadBelow headFirst tailFirst hPartsFirst.left generator hMem
              rw [← dlNatBeqEq headFirst generator hBeqHG] at hGenBelow
              rw [natBleRefl headFirst] at hGenBelow
              exact Bool.noConfusion hGenBelow
            | false =>
              rw [dlGenMemberConsFalse generator headFirst tailSecond hBeqHG] at hInSecond
              exact hInSecond
          have hTailSF : clauseSubset tailSecond tailFirst = true := by
            refine dlClauseSubsetIntro tailSecond tailFirst (fun generator hMem => ?_)
            have hInFirst : genMember generator (headFirst :: tailFirst) = true :=
              dlClauseSubsetElim tailSecond (headFirst :: tailFirst) hSF generator hMem
            cases hBeqHG : Nat.beq headFirst generator with
            | true =>
              have hGenBelow : natBle generator headFirst = false :=
                dlSortedHeadBelow headFirst tailSecond hPartsSecond.left generator hMem
              rw [← dlNatBeqEq headFirst generator hBeqHG] at hGenBelow
              rw [natBleRefl headFirst] at hGenBelow
              exact Bool.noConfusion hGenBelow
            | false =>
              rw [dlGenMemberConsFalse generator headFirst tailFirst hBeqHG] at hInFirst
              exact hInFirst
          rw [ih tailSecond hPartsFirst.right hPartsSecond.right hTailFS hTailSF]

/-! ## ROUND 2 — STEP 5b: DNF-level strict sortedness (the `clauseLess`-sorted clause list) -/

/-- Is the clause STRICTLY `clauseLess`-below every clause of the DNF?  The hereditary head condition of a
sorted DNF. -/
def dlIsBelowAllClauses (clause : List Nat) : List (List Nat) → Bool
  | [] => true
  | head :: rest =>
      match clauseLess clause head with
      | true => dlIsBelowAllClauses clause rest
      | false => false

/-- `dlIsBelowAllClauses` cons equation (BELOW): defer to the rest. -/
theorem dlBelowAllConsTrue (clause head : List Nat) (rest : List (List Nat))
    (h : clauseLess clause head = true) :
    dlIsBelowAllClauses clause (head :: rest) = dlIsBelowAllClauses clause rest := by
  show (match clauseLess clause head with
        | true => dlIsBelowAllClauses clause rest
        | false => false) = dlIsBelowAllClauses clause rest
  rw [h]

/-- `dlIsBelowAllClauses` cons equation (NOT BELOW): refuted. -/
theorem dlBelowAllConsFalse (clause head : List Nat) (rest : List (List Nat))
    (h : clauseLess clause head = false) :
    dlIsBelowAllClauses clause (head :: rest) = false := by
  show (match clauseLess clause head with
        | true => dlIsBelowAllClauses clause rest
        | false => false) = false
  rw [h]

/-- `dlIsBelowAllClauses` cons introduction. -/
theorem dlBelowAllConsIntro (clause head : List Nat) (rest : List (List Nat))
    (hHead : clauseLess clause head = true) (hRest : dlIsBelowAllClauses clause rest = true) :
    dlIsBelowAllClauses clause (head :: rest) = true := by
  rw [dlBelowAllConsTrue clause head rest hHead]
  exact hRest

/-- Is the DNF a STRICTLY `clauseLess`-sorted clause list (hereditary head bounds)?  The canonical DNF-level
invariant maintained by `insertClauseSorted`. -/
def dlIsSortedDnf : List (List Nat) → Bool
  | [] => true
  | clause :: rest =>
      match dlIsBelowAllClauses clause rest with
      | true => dlIsSortedDnf rest
      | false => false

/-- `dlIsSortedDnf` cons equation (HEAD BELOW ALL): defer to the rest. -/
theorem dlSortedDnfConsTrue (clause : List Nat) (rest : List (List Nat))
    (h : dlIsBelowAllClauses clause rest = true) :
    dlIsSortedDnf (clause :: rest) = dlIsSortedDnf rest := by
  show (match dlIsBelowAllClauses clause rest with
        | true => dlIsSortedDnf rest
        | false => false) = dlIsSortedDnf rest
  rw [h]

/-- `dlIsSortedDnf` cons equation (HEAD NOT BELOW ALL): refuted. -/
theorem dlSortedDnfConsFalse (clause : List Nat) (rest : List (List Nat))
    (h : dlIsBelowAllClauses clause rest = false) : dlIsSortedDnf (clause :: rest) = false := by
  show (match dlIsBelowAllClauses clause rest with
        | true => dlIsSortedDnf rest
        | false => false) = false
  rw [h]

/-- `dlIsSortedDnf` cons introduction. -/
theorem dlSortedDnfConsIntro (clause : List Nat) (rest : List (List Nat))
    (hBelow : dlIsBelowAllClauses clause rest = true) (hRest : dlIsSortedDnf rest = true) :
    dlIsSortedDnf (clause :: rest) = true := by
  rw [dlSortedDnfConsTrue clause rest hBelow]
  exact hRest

/-- `dlIsSortedDnf` cons elimination — both components of the invariant. -/
theorem dlSortedDnfConsElim (clause : List Nat) (rest : List (List Nat))
    (hSorted : dlIsSortedDnf (clause :: rest) = true) :
    dlIsBelowAllClauses clause rest = true ∧ dlIsSortedDnf rest = true := by
  cases hBelow : dlIsBelowAllClauses clause rest with
  | false =>
    rw [dlSortedDnfConsFalse clause rest hBelow] at hSorted
    exact Bool.noConfusion hSorted
  | true =>
    rw [dlSortedDnfConsTrue clause rest hBelow] at hSorted
    exact ⟨rfl, hSorted⟩

/-- A hereditary head bound reaches every member: `clause` below all of `dnf` and `member ∈ dnf` give
`clauseLess clause member = true`. -/
theorem dlBelowAllMember (clause : List Nat) : (dnf : List (List Nat)) →
    dlIsBelowAllClauses clause dnf = true → (member : List Nat) →
    dlDnfHasClause member dnf = true → clauseLess clause member = true := by
  intro dnf
  induction dnf with
  | nil => intro hBelow member hMem; exact Bool.noConfusion hMem
  | cons head rest ih =>
    intro hBelow member hMem
    cases hLess : clauseLess clause head with
    | false =>
      rw [dlBelowAllConsFalse clause head rest hLess] at hBelow
      exact Bool.noConfusion hBelow
    | true =>
      rw [dlBelowAllConsTrue clause head rest hLess] at hBelow
      cases hBeq : dlClauseBeq head member with
      | true => rw [← dlClauseBeqEq head member hBeq]; exact hLess
      | false =>
        rw [dlDnfHasClauseConsFalse member head rest hBeq] at hMem
        exact ih hBelow member hMem

/-- A strictly lower clause inherits a below-all bound: `lower < upper` (in `clauseLess`) and `upper` below
all of `dnf` give `lower` below all of `dnf` — by `dlClauseLessTrans`. -/
theorem dlBelowAllTrans (lower upper : List Nat) (hLU : clauseLess lower upper = true) :
    (dnf : List (List Nat)) → dlIsBelowAllClauses upper dnf = true →
    dlIsBelowAllClauses lower dnf = true := by
  intro dnf
  induction dnf with
  | nil => intro hBelow; rfl
  | cons head rest ih =>
    intro hBelow
    cases hLess : clauseLess upper head with
    | false =>
      rw [dlBelowAllConsFalse upper head rest hLess] at hBelow
      exact Bool.noConfusion hBelow
    | true =>
      rw [dlBelowAllConsTrue upper head rest hLess] at hBelow
      exact dlBelowAllConsIntro lower head rest (dlClauseLessTrans lower upper head hLU hLess) (ih hBelow)

/-- A below-all bound survives `removeSupersets` (a filter only drops clauses). -/
theorem dlBelowAllRemoveSupersets (clause candidate : List Nat) : (dnf : List (List Nat)) →
    dlIsBelowAllClauses clause dnf = true →
    dlIsBelowAllClauses clause (removeSupersets candidate dnf) = true := by
  intro dnf
  induction dnf with
  | nil => intro hBelow; rfl
  | cons head rest ih =>
    intro hBelow
    cases hLess : clauseLess clause head with
    | false =>
      rw [dlBelowAllConsFalse clause head rest hLess] at hBelow
      exact Bool.noConfusion hBelow
    | true =>
      rw [dlBelowAllConsTrue clause head rest hLess] at hBelow
      cases hSub : clauseSubset candidate head with
      | true =>
        rw [dlRemoveSupersetsConsDrop candidate head rest hSub]
        exact ih hBelow
      | false =>
        rw [dlRemoveSupersetsConsKeep candidate head rest hSub]
        exact dlBelowAllConsIntro clause head (removeSupersets candidate rest) hLess (ih hBelow)

/-- `removeSupersets` preserves DNF sortedness. -/
theorem dlSortedRemoveSupersets (candidate : List Nat) : (dnf : List (List Nat)) →
    dlIsSortedDnf dnf = true → dlIsSortedDnf (removeSupersets candidate dnf) = true := by
  intro dnf
  induction dnf with
  | nil => intro hSorted; rfl
  | cons head rest ih =>
    intro hSorted
    have hParts := dlSortedDnfConsElim head rest hSorted
    cases hSub : clauseSubset candidate head with
    | true =>
      rw [dlRemoveSupersetsConsDrop candidate head rest hSub]
      exact ih hParts.right
    | false =>
      rw [dlRemoveSupersetsConsKeep candidate head rest hSub]
      exact dlSortedDnfConsIntro head (removeSupersets candidate rest)
        (dlBelowAllRemoveSupersets head candidate rest hParts.left) (ih hParts.right)

/-- A below-all bound strictly under the candidate survives `insertClauseSorted`. -/
theorem dlBelowAllInsertSorted (bound candidate : List Nat) (hBC : clauseLess bound candidate = true) :
    (dnf : List (List Nat)) → dlIsBelowAllClauses bound dnf = true →
    dlIsBelowAllClauses bound (insertClauseSorted candidate dnf) = true := by
  intro dnf
  induction dnf with
  | nil =>
    intro hBelow
    show dlIsBelowAllClauses bound [candidate] = true
    exact dlBelowAllConsIntro bound candidate [] hBC rfl
  | cons head rest ih =>
    intro hBelow
    cases hLess : clauseLess bound head with
    | false =>
      rw [dlBelowAllConsFalse bound head rest hLess] at hBelow
      exact Bool.noConfusion hBelow
    | true =>
      rw [dlBelowAllConsTrue bound head rest hLess] at hBelow
      cases hCH : clauseLess candidate head with
      | true =>
        rw [dlInsertClauseSortedLt candidate head rest hCH]
        exact dlBelowAllConsIntro bound candidate (head :: rest) hBC
          (dlBelowAllConsIntro bound head rest hLess hBelow)
      | false =>
        cases hHC : clauseLess head candidate with
        | true =>
          rw [dlInsertClauseSortedGt candidate head rest hCH hHC]
          exact dlBelowAllConsIntro bound head (insertClauseSorted candidate rest) hLess (ih hBelow)
        | false =>
          rw [dlInsertClauseSortedEq candidate head rest hCH hHC]
          exact dlBelowAllConsIntro bound head rest hLess hBelow

/-- ★ `insertClauseSorted` preserves DNF sortedness — the front insert extends the head bound via
`dlBelowAllTrans` (this is where `clauseLess` transitivity earns its keep). -/
theorem dlSortedInsertClauseSorted (candidate : List Nat) : (dnf : List (List Nat)) →
    dlIsSortedDnf dnf = true → dlIsSortedDnf (insertClauseSorted candidate dnf) = true := by
  intro dnf
  induction dnf with
  | nil =>
    intro hSorted
    exact dlSortedDnfConsIntro candidate [] rfl rfl
  | cons head rest ih =>
    intro hSorted
    have hParts := dlSortedDnfConsElim head rest hSorted
    cases hCH : clauseLess candidate head with
    | true =>
      rw [dlInsertClauseSortedLt candidate head rest hCH]
      exact dlSortedDnfConsIntro candidate (head :: rest)
        (dlBelowAllConsIntro candidate head rest hCH (dlBelowAllTrans candidate head hCH rest hParts.left))
        hSorted
    | false =>
      cases hHC : clauseLess head candidate with
      | true =>
        rw [dlInsertClauseSortedGt candidate head rest hCH hHC]
        exact dlSortedDnfConsIntro head (insertClauseSorted candidate rest)
          (dlBelowAllInsertSorted head candidate hHC rest hParts.left) (ih hParts.right)
      | false =>
        rw [dlInsertClauseSortedEq candidate head rest hCH hHC]
        exact hSorted

/-- ★ `insertClause` preserves DNF sortedness. -/
theorem dlSortedInsertClause (candidate : List Nat) (dnf : List (List Nat))
    (hSorted : dlIsSortedDnf dnf = true) : dlIsSortedDnf (insertClause candidate dnf) = true := by
  cases hHas : dnfHasSubsetOf candidate dnf with
  | true =>
    rw [dlInsertClauseAbsorbed candidate dnf hHas]
    exact hSorted
  | false =>
    rw [dlInsertClauseFresh candidate dnf hHas]
    exact dlSortedInsertClauseSorted candidate (removeSupersets candidate dnf)
      (dlSortedRemoveSupersets candidate dnf hSorted)

/-- `dnfUnion` preserves DNF sortedness of the accumulator. -/
theorem dlSortedDnfUnion : (first : List (List Nat)) → (second : List (List Nat)) →
    dlIsSortedDnf second = true → dlIsSortedDnf (dnfUnion first second) = true := by
  intro first
  induction first with
  | nil => intro second hSorted; exact hSorted
  | cons clause rest ih =>
    intro second hSorted
    show dlIsSortedDnf (insertClause clause (dnfUnion rest second)) = true
    exact dlSortedInsertClause clause (dnfUnion rest second) (ih second hSorted)

/-- `dnfMeetClause` output is sorted (built by `insertClause` from the empty antichain). -/
theorem dlSortedDnfMeetClause (factor : List Nat) : (other : List (List Nat)) →
    dlIsSortedDnf (dnfMeetClause factor other) = true
  | [] => rfl
  | clause :: rest => by
      show dlIsSortedDnf (insertClause (insertManySet factor clause) (dnfMeetClause factor rest)) = true
      exact dlSortedInsertClause (insertManySet factor clause) (dnfMeetClause factor rest)
        (dlSortedDnfMeetClause factor rest)

/-- `dnfMeet` output is sorted. -/
theorem dlSortedDnfMeet : (first second : List (List Nat)) → dlIsSortedDnf (dnfMeet first second) = true
  | [], _ => rfl
  | clause :: rest, second => by
      show dlIsSortedDnf (dnfUnion (dnfMeetClause clause second) (dnfMeet rest second)) = true
      exact dlSortedDnfUnion (dnfMeetClause clause second) (dnfMeet rest second)
        (dlSortedDnfMeet rest second)

/-- ★ **The canonical DNF is sorted** — `dnfOf` output satisfies the strict DNF-level sortedness. -/
theorem dlSortedDnfOf : (tree : LatticeTree) → dlIsSortedDnf (dnfOf tree) = true
  | .gen _ => rfl
  | .topOp => rfl
  | .botOp => rfl
  | .meetOp left right => dlSortedDnfMeet (dnfOf left) (dnfOf right)
  | .joinOp left right => dlSortedDnfUnion (dnfOf left) (dnfOf right) (dlSortedDnfOf right)

/-! ## ROUND 2 — STEP 5c: every clause of the canonical DNF is itself sorted-distinct -/

/-- Are ALL clauses of the DNF strictly sorted generator lists? -/
def dlAreClausesSorted : List (List Nat) → Bool
  | [] => true
  | clause :: rest =>
      match dlIsSortedClause clause with
      | true => dlAreClausesSorted rest
      | false => false

/-- `dlAreClausesSorted` cons equation (HEAD SORTED): defer to the rest. -/
theorem dlClausesSortedConsTrue (clause : List Nat) (rest : List (List Nat))
    (h : dlIsSortedClause clause = true) :
    dlAreClausesSorted (clause :: rest) = dlAreClausesSorted rest := by
  show (match dlIsSortedClause clause with
        | true => dlAreClausesSorted rest
        | false => false) = dlAreClausesSorted rest
  rw [h]

/-- `dlAreClausesSorted` cons equation (HEAD UNSORTED): refuted. -/
theorem dlClausesSortedConsFalse (clause : List Nat) (rest : List (List Nat))
    (h : dlIsSortedClause clause = false) : dlAreClausesSorted (clause :: rest) = false := by
  show (match dlIsSortedClause clause with
        | true => dlAreClausesSorted rest
        | false => false) = false
  rw [h]

/-- `dlAreClausesSorted` cons introduction. -/
theorem dlClausesSortedConsIntro (clause : List Nat) (rest : List (List Nat))
    (hClause : dlIsSortedClause clause = true) (hRest : dlAreClausesSorted rest = true) :
    dlAreClausesSorted (clause :: rest) = true := by
  rw [dlClausesSortedConsTrue clause rest hClause]
  exact hRest

/-- `dlAreClausesSorted` cons elimination. -/
theorem dlClausesSortedConsElim (clause : List Nat) (rest : List (List Nat))
    (hAll : dlAreClausesSorted (clause :: rest) = true) :
    dlIsSortedClause clause = true ∧ dlAreClausesSorted rest = true := by
  cases hClause : dlIsSortedClause clause with
  | false =>
    rw [dlClausesSortedConsFalse clause rest hClause] at hAll
    exact Bool.noConfusion hAll
  | true =>
    rw [dlClausesSortedConsTrue clause rest hClause] at hAll
    exact ⟨rfl, hAll⟩

/-- Every member of a clauses-sorted DNF is a sorted clause. -/
theorem dlAreClausesSortedMember : (dnf : List (List Nat)) → dlAreClausesSorted dnf = true →
    (member : List Nat) → dlDnfHasClause member dnf = true → dlIsSortedClause member = true := by
  intro dnf
  induction dnf with
  | nil => intro hAll member hMem; exact Bool.noConfusion hMem
  | cons clause rest ih =>
    intro hAll member hMem
    have hParts := dlClausesSortedConsElim clause rest hAll
    cases hBeq : dlClauseBeq clause member with
    | true => rw [← dlClauseBeqEq clause member hBeq]; exact hParts.left
    | false =>
      rw [dlDnfHasClauseConsFalse member clause rest hBeq] at hMem
      exact ih hParts.right member hMem

/-- `removeSupersets` preserves the clauses-sorted invariant (a filter). -/
theorem dlClausesSortedRemoveSupersets (candidate : List Nat) : (dnf : List (List Nat)) →
    dlAreClausesSorted dnf = true → dlAreClausesSorted (removeSupersets candidate dnf) = true := by
  intro dnf
  induction dnf with
  | nil => intro hAll; rfl
  | cons head rest ih =>
    intro hAll
    have hParts := dlClausesSortedConsElim head rest hAll
    cases hSub : clauseSubset candidate head with
    | true =>
      rw [dlRemoveSupersetsConsDrop candidate head rest hSub]
      exact ih hParts.right
    | false =>
      rw [dlRemoveSupersetsConsKeep candidate head rest hSub]
      exact dlClausesSortedConsIntro head (removeSupersets candidate rest) hParts.left (ih hParts.right)

/-- `insertClauseSorted` preserves the clauses-sorted invariant when the candidate clause is sorted. -/
theorem dlClausesSortedInsertClauseSorted (candidate : List Nat)
    (hCand : dlIsSortedClause candidate = true) : (dnf : List (List Nat)) →
    dlAreClausesSorted dnf = true → dlAreClausesSorted (insertClauseSorted candidate dnf) = true := by
  intro dnf
  induction dnf with
  | nil =>
    intro hAll
    exact dlClausesSortedConsIntro candidate [] hCand rfl
  | cons head rest ih =>
    intro hAll
    have hParts := dlClausesSortedConsElim head rest hAll
    cases hCH : clauseLess candidate head with
    | true =>
      rw [dlInsertClauseSortedLt candidate head rest hCH]
      exact dlClausesSortedConsIntro candidate (head :: rest) hCand hAll
    | false =>
      cases hHC : clauseLess head candidate with
      | true =>
        rw [dlInsertClauseSortedGt candidate head rest hCH hHC]
        exact dlClausesSortedConsIntro head (insertClauseSorted candidate rest) hParts.left
          (ih hParts.right)
      | false =>
        rw [dlInsertClauseSortedEq candidate head rest hCH hHC]
        exact hAll

/-- `insertClause` preserves the clauses-sorted invariant when the candidate clause is sorted. -/
theorem dlClausesSortedInsertClause (candidate : List Nat)
    (hCand : dlIsSortedClause candidate = true) (dnf : List (List Nat))
    (hAll : dlAreClausesSorted dnf = true) :
    dlAreClausesSorted (insertClause candidate dnf) = true := by
  cases hHas : dnfHasSubsetOf candidate dnf with
  | true =>
    rw [dlInsertClauseAbsorbed candidate dnf hHas]
    exact hAll
  | false =>
    rw [dlInsertClauseFresh candidate dnf hHas]
    exact dlClausesSortedInsertClauseSorted candidate hCand (removeSupersets candidate dnf)
      (dlClausesSortedRemoveSupersets candidate dnf hAll)

/-- `dnfUnion` preserves the clauses-sorted invariant of both inputs. -/
theorem dlClausesSortedDnfUnion : (first : List (List Nat)) → (second : List (List Nat)) →
    dlAreClausesSorted first = true → dlAreClausesSorted second = true →
    dlAreClausesSorted (dnfUnion first second) = true := by
  intro first
  induction first with
  | nil => intro second hFirst hSecond; exact hSecond
  | cons clause rest ih =>
    intro second hFirst hSecond
    have hParts := dlClausesSortedConsElim clause rest hFirst
    show dlAreClausesSorted (insertClause clause (dnfUnion rest second)) = true
    exact dlClausesSortedInsertClause clause hParts.left (dnfUnion rest second)
      (ih second hParts.right hSecond)

/-- `dnfMeetClause` output has sorted clauses — each inserted clause is `insertManySet factor clause` with
`clause` a sorted clause of the second input (`dlSortedClauseInsertMany`). -/
theorem dlClausesSortedDnfMeetClause (factor : List Nat) : (other : List (List Nat)) →
    dlAreClausesSorted other = true → dlAreClausesSorted (dnfMeetClause factor other) = true := by
  intro other
  induction other with
  | nil => intro hOther; rfl
  | cons clause rest ih =>
    intro hOther
    have hParts := dlClausesSortedConsElim clause rest hOther
    show dlAreClausesSorted (insertClause (insertManySet factor clause) (dnfMeetClause factor rest)) = true
    exact dlClausesSortedInsertClause (insertManySet factor clause)
      (dlSortedClauseInsertMany factor clause hParts.left) (dnfMeetClause factor rest) (ih hParts.right)

/-- `dnfMeet` output has sorted clauses (only the second input's clause sortedness is consumed). -/
theorem dlClausesSortedDnfMeet : (first second : List (List Nat)) →
    dlAreClausesSorted second = true → dlAreClausesSorted (dnfMeet first second) = true
  | [], _, _ => rfl
  | clause :: rest, second, hSecond => by
      show dlAreClausesSorted (dnfUnion (dnfMeetClause clause second) (dnfMeet rest second)) = true
      exact dlClausesSortedDnfUnion (dnfMeetClause clause second) (dnfMeet rest second)
        (dlClausesSortedDnfMeetClause clause second hSecond)
        (dlClausesSortedDnfMeet rest second hSecond)

/-- ★ **Every clause of the canonical DNF is sorted-distinct** — `dnfOf` output satisfies the clause-level
sortedness. -/
theorem dlClausesSortedDnfOf : (tree : LatticeTree) → dlAreClausesSorted (dnfOf tree) = true
  | .gen _ => rfl
  | .topOp => rfl
  | .botOp => rfl
  | .meetOp left right => dlClausesSortedDnfMeet (dnfOf left) (dnfOf right) (dlClausesSortedDnfOf right)
  | .joinOp left right => dlClausesSortedDnfUnion (dnfOf left) (dnfOf right)
      (dlClausesSortedDnfOf left) (dlClausesSortedDnfOf right)

/-! ## ROUND 2 — STEP 5d: the antichain invariant (no clause contains a different clause) -/

/-- ★ The **antichain property** of a DNF — any member clause contained in another member clause EQUALS it.
The ⊆-minimality that makes the canonical DNF the unique irredundant representative (Quine: the prime
implicants of a positive Boolean function). -/
def dlDnfIsAntichain (dnf : List (List Nat)) : Prop :=
  ∀ first second : List Nat, dlDnfHasClause first dnf = true → dlDnfHasClause second dnf = true →
    clauseSubset first second = true → first = second

/-- A member with a containment witnesses the absorption scan: `witness ∈ dnf` and `witness ⊆ candidate`
give `dnfHasSubsetOf candidate dnf = true`. -/
theorem dlHasSubsetOfIntro (candidate : List Nat) : (dnf : List (List Nat)) → (witness : List Nat) →
    dlDnfHasClause witness dnf = true → clauseSubset witness candidate = true →
    dnfHasSubsetOf candidate dnf = true := by
  intro dnf
  induction dnf with
  | nil => intro witness hMem hSub; exact Bool.noConfusion hMem
  | cons clause rest ih =>
    intro witness hMem hSub
    cases hCS : clauseSubset clause candidate with
    | true => exact dlHasSubsetConsTrue candidate clause rest hCS
    | false =>
      rw [dlHasSubsetConsFalse candidate clause rest hCS]
      cases hBeq : dlClauseBeq clause witness with
      | true =>
        rw [← dlClauseBeqEq clause witness hBeq] at hSub
        rw [hSub] at hCS
        exact Bool.noConfusion hCS
      | false =>
        rw [dlDnfHasClauseConsFalse witness clause rest hBeq] at hMem
        exact ih witness hMem hSub

/-- The absorption scan yields a member with a containment: `dnfHasSubsetOf candidate dnf = true` produces
a clause of `dnf` contained in `candidate`. -/
theorem dlHasSubsetOfExists (candidate : List Nat) : (dnf : List (List Nat)) →
    dnfHasSubsetOf candidate dnf = true →
    ∃ witness : List Nat, dlDnfHasClause witness dnf = true ∧ clauseSubset witness candidate = true := by
  intro dnf
  induction dnf with
  | nil => intro hHas; exact Bool.noConfusion hHas
  | cons clause rest ih =>
    intro hHas
    cases hCS : clauseSubset clause candidate with
    | true => exact ⟨clause, dlDnfHasClauseHead clause rest, hCS⟩
    | false =>
      rw [dlHasSubsetConsFalse candidate clause rest hCS] at hHas
      have ⟨witness, hMem, hSub⟩ := ih hHas
      exact ⟨witness, dlDnfHasClauseConsWeaken witness clause rest hMem, hSub⟩

/-- A failed absorption scan refutes containment for every member. -/
theorem dlHasSubsetOfFalseMember (candidate : List Nat) : (dnf : List (List Nat)) →
    dnfHasSubsetOf candidate dnf = false → (member : List Nat) → dlDnfHasClause member dnf = true →
    clauseSubset member candidate = false := by
  intro dnf
  induction dnf with
  | nil => intro hHas member hMem; exact Bool.noConfusion hMem
  | cons clause rest ih =>
    intro hHas member hMem
    cases hCS : clauseSubset clause candidate with
    | true =>
      rw [dlHasSubsetConsTrue candidate clause rest hCS] at hHas
      exact Bool.noConfusion hHas
    | false =>
      rw [dlHasSubsetConsFalse candidate clause rest hCS] at hHas
      cases hBeq : dlClauseBeq clause member with
      | true => rw [← dlClauseBeqEq clause member hBeq]; exact hCS
      | false =>
        rw [dlDnfHasClauseConsFalse member clause rest hBeq] at hMem
        exact ih hHas member hMem

/-- Membership in `removeSupersets` reflects to the original DNF and certifies the kept clause is NOT a
superset of the candidate. -/
theorem dlMemRemoveSupersets (candidate member : List Nat) : (dnf : List (List Nat)) →
    dlDnfHasClause member (removeSupersets candidate dnf) = true →
    dlDnfHasClause member dnf = true ∧ clauseSubset candidate member = false := by
  intro dnf
  induction dnf with
  | nil => intro hMem; exact Bool.noConfusion hMem
  | cons clause rest ih =>
    intro hMem
    cases hCS : clauseSubset candidate clause with
    | true =>
      rw [dlRemoveSupersetsConsDrop candidate clause rest hCS] at hMem
      have hRec := ih hMem
      exact ⟨dlDnfHasClauseConsWeaken member clause rest hRec.left, hRec.right⟩
    | false =>
      rw [dlRemoveSupersetsConsKeep candidate clause rest hCS] at hMem
      cases hBeq : dlClauseBeq clause member with
      | true =>
        refine ⟨dlDnfHasClauseConsTrue member clause rest hBeq, ?_⟩
        rw [← dlClauseBeqEq clause member hBeq]
        exact hCS
      | false =>
        rw [dlDnfHasClauseConsFalse member clause (removeSupersets candidate rest) hBeq] at hMem
        have hRec := ih hMem
        exact ⟨dlDnfHasClauseConsWeaken member clause rest hRec.left, hRec.right⟩

/-- Membership in `insertClauseSorted` is the candidate or an original member. -/
theorem dlMemInsertClauseSorted (candidate member : List Nat) : (dnf : List (List Nat)) →
    dlDnfHasClause member (insertClauseSorted candidate dnf) = true →
    candidate = member ∨ dlDnfHasClause member dnf = true := by
  intro dnf
  induction dnf with
  | nil =>
    intro hMem
    have hSingle : dlDnfHasClause member [candidate] = true := hMem
    cases hBeq : dlClauseBeq candidate member with
    | true => exact Or.inl (dlClauseBeqEq candidate member hBeq)
    | false =>
      rw [dlDnfHasClauseConsFalse member candidate [] hBeq] at hSingle
      exact Bool.noConfusion hSingle
  | cons clause rest ih =>
    intro hMem
    cases hCH : clauseLess candidate clause with
    | true =>
      rw [dlInsertClauseSortedLt candidate clause rest hCH] at hMem
      cases hBeq : dlClauseBeq candidate member with
      | true => exact Or.inl (dlClauseBeqEq candidate member hBeq)
      | false =>
        rw [dlDnfHasClauseConsFalse member candidate (clause :: rest) hBeq] at hMem
        exact Or.inr hMem
    | false =>
      cases hHC : clauseLess clause candidate with
      | true =>
        rw [dlInsertClauseSortedGt candidate clause rest hCH hHC] at hMem
        cases hBeq : dlClauseBeq clause member with
        | true => exact Or.inr (dlDnfHasClauseConsTrue member clause rest hBeq)
        | false =>
          rw [dlDnfHasClauseConsFalse member clause (insertClauseSorted candidate rest) hBeq] at hMem
          cases ih hMem with
          | inl hEq => exact Or.inl hEq
          | inr hRest => exact Or.inr (dlDnfHasClauseConsWeaken member clause rest hRest)
      | false =>
        rw [dlInsertClauseSortedEq candidate clause rest hCH hHC] at hMem
        exact Or.inr hMem

/-- Membership in `insertClause` is the candidate or an original member. -/
theorem dlMemInsertClause (candidate member : List Nat) (dnf : List (List Nat))
    (hMem : dlDnfHasClause member (insertClause candidate dnf) = true) :
    candidate = member ∨ dlDnfHasClause member dnf = true := by
  cases hHas : dnfHasSubsetOf candidate dnf with
  | true =>
    rw [dlInsertClauseAbsorbed candidate dnf hHas] at hMem
    exact Or.inr hMem
  | false =>
    rw [dlInsertClauseFresh candidate dnf hHas] at hMem
    cases dlMemInsertClauseSorted candidate member (removeSupersets candidate dnf) hMem with
    | inl hEq => exact Or.inl hEq
    | inr hKept => exact Or.inr (dlMemRemoveSupersets candidate member dnf hKept).left

/-- The empty DNF is an antichain. -/
theorem dlNilDnfIsAntichain : dlDnfIsAntichain [] := by
  intro first second hFirst hSecond hSub
  exact Bool.noConfusion hFirst

/-- A one-clause DNF is an antichain. -/
theorem dlSingletonDnfIsAntichain (clause : List Nat) : dlDnfIsAntichain [clause] := by
  intro first second hFirst hSecond hSub
  cases hBeqF : dlClauseBeq clause first with
  | false =>
    rw [dlDnfHasClauseConsFalse first clause [] hBeqF] at hFirst
    exact Bool.noConfusion hFirst
  | true =>
    cases hBeqS : dlClauseBeq clause second with
    | false =>
      rw [dlDnfHasClauseConsFalse second clause [] hBeqS] at hSecond
      exact Bool.noConfusion hSecond
    | true =>
      rw [← dlClauseBeqEq clause first hBeqF, ← dlClauseBeqEq clause second hBeqS]

/-- ★ **`insertClause` preserves the antichain property.**  Absorbed candidates change nothing.  A fresh
candidate is incomparable with every kept clause: the kept clause is not a superset of the candidate
(`dlMemRemoveSupersets`), and no original clause — hence no kept clause — is a subset of the candidate
(`dlHasSubsetOfFalseMember` on the failed absorption scan). -/
theorem dlInsertClauseAntichain (candidate : List Nat) (dnf : List (List Nat))
    (hAnti : dlDnfIsAntichain dnf) : dlDnfIsAntichain (insertClause candidate dnf) := by
  intro first second hFirst hSecond hSub
  cases hHas : dnfHasSubsetOf candidate dnf with
  | true =>
    rw [dlInsertClauseAbsorbed candidate dnf hHas] at hFirst hSecond
    exact hAnti first second hFirst hSecond hSub
  | false =>
    rw [dlInsertClauseFresh candidate dnf hHas] at hFirst hSecond
    cases dlMemInsertClauseSorted candidate first (removeSupersets candidate dnf) hFirst with
    | inl hEqFirst =>
      cases dlMemInsertClauseSorted candidate second (removeSupersets candidate dnf) hSecond with
      | inl hEqSecond => rw [← hEqFirst, ← hEqSecond]
      | inr hKeptSecond =>
        have hFacts := dlMemRemoveSupersets candidate second dnf hKeptSecond
        rw [← hEqFirst] at hSub
        rw [hFacts.right] at hSub
        exact Bool.noConfusion hSub
    | inr hKeptFirst =>
      have hFactsFirst := dlMemRemoveSupersets candidate first dnf hKeptFirst
      cases dlMemInsertClauseSorted candidate second (removeSupersets candidate dnf) hSecond with
      | inl hEqSecond =>
        rw [← hEqSecond] at hSub
        have hNoSub : clauseSubset first candidate = false :=
          dlHasSubsetOfFalseMember candidate dnf hHas first hFactsFirst.left
        rw [hNoSub] at hSub
        exact Bool.noConfusion hSub
      | inr hKeptSecond =>
        have hFactsSecond := dlMemRemoveSupersets candidate second dnf hKeptSecond
        exact hAnti first second hFactsFirst.left hFactsSecond.left hSub

/-- `dnfUnion` preserves the antichain property of the accumulator. -/
theorem dlDnfUnionAntichain : (first : List (List Nat)) → (second : List (List Nat)) →
    dlDnfIsAntichain second → dlDnfIsAntichain (dnfUnion first second)
  | [], _, hAnti => hAnti
  | clause :: rest, second, hAnti =>
      dlInsertClauseAntichain clause (dnfUnion rest second) (dlDnfUnionAntichain rest second hAnti)

/-- `dnfMeetClause` output is an antichain. -/
theorem dlDnfMeetClauseAntichain (factor : List Nat) : (other : List (List Nat)) →
    dlDnfIsAntichain (dnfMeetClause factor other)
  | [] => dlNilDnfIsAntichain
  | clause :: rest =>
      dlInsertClauseAntichain (insertManySet factor clause) (dnfMeetClause factor rest)
        (dlDnfMeetClauseAntichain factor rest)

/-- `dnfMeet` output is an antichain. -/
theorem dlDnfMeetAntichain : (first second : List (List Nat)) → dlDnfIsAntichain (dnfMeet first second)
  | [], _ => dlNilDnfIsAntichain
  | clause :: rest, second =>
      dlDnfUnionAntichain (dnfMeetClause clause second) (dnfMeet rest second)
        (dlDnfMeetAntichain rest second)

/-- ★ **The canonical DNF is an antichain** — `dnfOf` output satisfies ⊆-minimality. -/
theorem dlDnfOfAntichain : (tree : LatticeTree) → dlDnfIsAntichain (dnfOf tree)
  | .gen colour => dlSingletonDnfIsAntichain [colour]
  | .topOp => dlSingletonDnfIsAntichain []
  | .botOp => dlNilDnfIsAntichain
  | .meetOp left right => dlDnfMeetAntichain (dnfOf left) (dnfOf right)
  | .joinOp left right => dlDnfUnionAntichain (dnfOf left) (dnfOf right) (dlDnfOfAntichain right)

/-! ## ROUND 2 — STEPS 6–7: membership transfer and canonical-DNF uniqueness -/

/-- ★ **Membership transfers along evaluation agreement** — the prime-implicant recovery.  If `first` is an
antichain with sorted clauses, `second` has sorted clauses, and the two DNFs evaluate equally under EVERY
environment, then every clause of `first` is a clause of `second`.  The clause `member` is recovered from the
Boolean function at two kinds of characteristic points: `chi member` produces a covering clause `witness ⊆
member` of `second`; if `witness ⊊ member` misses a generator, `chi (member \ {missing})` transports back to
a `first`-clause `cover ⊆ member \ {missing} ⊆ member`, which the ANTICHAIN forces to equal `member` — a
contradiction with the erased generator.  Hence `witness = member` by mutual containment on sorted clauses
(`dlClauseSubsetAntisymm`). -/
theorem dlCanonicalMemberTransfers (first second : List (List Nat))
    (hAntiFirst : dlDnfIsAntichain first)
    (hClausesFirst : dlAreClausesSorted first = true)
    (hClausesSecond : dlAreClausesSorted second = true)
    (hAgree : ∀ env : Nat → Bool, dlEvalDnf env first = dlEvalDnf env second)
    (member : List Nat) (hMem : dlDnfHasClause member first = true) :
    dlDnfHasClause member second = true := by
  have hMemSorted : dlIsSortedClause member = true :=
    dlAreClausesSortedMember first hClausesFirst member hMem
  have hHasFirst : dnfHasSubsetOf member first = true :=
    dlHasSubsetOfIntro member first member hMem (dlClauseSubsetRefl member)
  have hHasSecond : dnfHasSubsetOf member second = true := by
    rw [← dlEvalDnfChar member second, ← hAgree (dlCharacteristicEnv member),
        dlEvalDnfChar member first]
    exact hHasFirst
  have ⟨witness, hWitMem, hWitSub⟩ := dlHasSubsetOfExists member second hHasSecond
  have hWitSorted : dlIsSortedClause witness = true :=
    dlAreClausesSortedMember second hClausesSecond witness hWitMem
  cases hMW : clauseSubset member witness with
  | true =>
    rw [dlClauseSubsetAntisymm witness member hWitSorted hMemSorted hWitSub hMW] at hWitMem
    exact hWitMem
  | false =>
    have ⟨missing, hMissMem, hMissAbsent⟩ := dlClauseSubsetFalseWitness member witness hMW
    have hWitErase : clauseSubset witness (dlEraseGenerator missing member) = true :=
      dlClauseSubsetEraseIntro witness member missing hWitSub hMissAbsent
    have hHasEraseSecond : dnfHasSubsetOf (dlEraseGenerator missing member) second = true :=
      dlHasSubsetOfIntro (dlEraseGenerator missing member) second witness hWitMem hWitErase
    have hHasEraseFirst : dnfHasSubsetOf (dlEraseGenerator missing member) first = true := by
      rw [← dlEvalDnfChar (dlEraseGenerator missing member) first,
          hAgree (dlCharacteristicEnv (dlEraseGenerator missing member)),
          dlEvalDnfChar (dlEraseGenerator missing member) second]
      exact hHasEraseSecond
    have ⟨cover, hCoverMem, hCoverSub⟩ :=
      dlHasSubsetOfExists (dlEraseGenerator missing member) first hHasEraseFirst
    have hCoverMemberSub : clauseSubset cover member = true :=
      dlClauseSubsetTrans cover (dlEraseGenerator missing member) member hCoverSub
        (dlEraseSubset missing member)
    have hCoverEq : cover = member := hAntiFirst cover member hCoverMem hMem hCoverMemberSub
    rw [hCoverEq] at hCoverSub
    have hMissErase : genMember missing (dlEraseGenerator missing member) = true :=
      dlClauseSubsetElim member (dlEraseGenerator missing member) hCoverSub missing hMissMem
    rw [dlGenMemberEraseSelf missing member] at hMissErase
    exact Bool.noConfusion hMissErase

/-- ★ **Sorted-DNF extensionality** — two strictly sorted DNFs with the same Boolean clause membership are
EQUAL lists.  Double descent: the heads coincide (each is a member of the other list, and a sorted head is
the strict `clauseLess` minimum — a clash falls to `dlClauseLessAsymm`), and the shared head cannot recur in
either tail (`dlClauseLessIrrefl`), so the tail memberships agree and the induction closes. -/
theorem dlSortedDnfMembersEq : (first : List (List Nat)) → (second : List (List Nat)) →
    dlIsSortedDnf first = true → dlIsSortedDnf second = true →
    (∀ member : List Nat, dlDnfHasClause member first = dlDnfHasClause member second) →
    first = second := by
  intro first
  induction first with
  | nil =>
    intro second hSortedFirst hSortedSecond hSame
    cases second with
    | nil => rfl
    | cons headSecond tailSecond =>
      have hAbsurd : dlDnfHasClause headSecond ([] : List (List Nat)) = true := by
        rw [hSame headSecond]
        exact dlDnfHasClauseHead headSecond tailSecond
      exact Bool.noConfusion hAbsurd
  | cons headFirst tailFirst ih =>
    intro second hSortedFirst hSortedSecond hSame
    cases second with
    | nil =>
      have hAbsurd : dlDnfHasClause headFirst ([] : List (List Nat)) = true := by
        rw [← hSame headFirst]
        exact dlDnfHasClauseHead headFirst tailFirst
      exact Bool.noConfusion hAbsurd
    | cons headSecond tailSecond =>
      have hPartsFirst := dlSortedDnfConsElim headFirst tailFirst hSortedFirst
      have hPartsSecond := dlSortedDnfConsElim headSecond tailSecond hSortedSecond
      have hHeadEq : headFirst = headSecond := by
        have hMemFS : dlDnfHasClause headFirst (headSecond :: tailSecond) = true := by
          rw [← hSame headFirst]
          exact dlDnfHasClauseHead headFirst tailFirst
        have hMemSF : dlDnfHasClause headSecond (headFirst :: tailFirst) = true := by
          rw [hSame headSecond]
          exact dlDnfHasClauseHead headSecond tailSecond
        cases hBeqSF : dlClauseBeq headSecond headFirst with
        | true => exact (dlClauseBeqEq headSecond headFirst hBeqSF).symm
        | false =>
          rw [dlDnfHasClauseConsFalse headFirst headSecond tailSecond hBeqSF] at hMemFS
          have hLessSF : clauseLess headSecond headFirst = true :=
            dlBelowAllMember headSecond tailSecond hPartsSecond.left headFirst hMemFS
          cases hBeqFS : dlClauseBeq headFirst headSecond with
          | true => exact dlClauseBeqEq headFirst headSecond hBeqFS
          | false =>
            rw [dlDnfHasClauseConsFalse headSecond headFirst tailFirst hBeqFS] at hMemSF
            have hLessFS : clauseLess headFirst headSecond = true :=
              dlBelowAllMember headFirst tailFirst hPartsFirst.left headSecond hMemSF
            have hAsym : clauseLess headSecond headFirst = false :=
              dlClauseLessAsymm headFirst headSecond hLessFS
            rw [hAsym] at hLessSF
            exact Bool.noConfusion hLessSF
      subst hHeadEq
      have hTailSame : ∀ member : List Nat,
          dlDnfHasClause member tailFirst = dlDnfHasClause member tailSecond := by
        intro member
        cases hBeq : dlClauseBeq headFirst member with
        | false =>
          have hStep := hSame member
          rw [dlDnfHasClauseConsFalse member headFirst tailFirst hBeq,
              dlDnfHasClauseConsFalse member headFirst tailSecond hBeq] at hStep
          exact hStep
        | true =>
          have hMemEq : headFirst = member := dlClauseBeqEq headFirst member hBeq
          cases hMemTailFirst : dlDnfHasClause member tailFirst with
          | true =>
            have hLess : clauseLess headFirst member = true :=
              dlBelowAllMember headFirst tailFirst hPartsFirst.left member hMemTailFirst
            rw [← hMemEq] at hLess
            rw [dlClauseLessIrrefl headFirst] at hLess
            exact Bool.noConfusion hLess
          | false =>
            cases hMemTailSecond : dlDnfHasClause member tailSecond with
            | true =>
              have hLess : clauseLess headFirst member = true :=
                dlBelowAllMember headFirst tailSecond hPartsSecond.left member hMemTailSecond
              rw [← hMemEq] at hLess
              rw [dlClauseLessIrrefl headFirst] at hLess
              exact Bool.noConfusion hLess
            | false => rfl
      rw [ih tailSecond hPartsFirst.right hPartsSecond.right hTailSame]

/-- ★★ **CANONICAL-DNF UNIQUENESS** — two canonical DNFs (strictly sorted antichains of sorted clauses)
computing the same monotone Boolean function are EQUAL lists.  Membership agrees in both directions by
`dlCanonicalMemberTransfers`; sorted extensionality finishes.  This is the classical uniqueness of the
irredundant DNF of a positive Boolean function (Quine 1954; Balbes–Dwinger's free distributive lattice as
irredundant antichains), machine-checked with only finitely many characteristic-environment probes. -/
theorem dlCanonicalDnfUnique (first second : List (List Nat))
    (hSortedFirst : dlIsSortedDnf first = true) (hSortedSecond : dlIsSortedDnf second = true)
    (hClausesFirst : dlAreClausesSorted first = true) (hClausesSecond : dlAreClausesSorted second = true)
    (hAntiFirst : dlDnfIsAntichain first) (hAntiSecond : dlDnfIsAntichain second)
    (hAgree : ∀ env : Nat → Bool, dlEvalDnf env first = dlEvalDnf env second) :
    first = second := by
  refine dlSortedDnfMembersEq first second hSortedFirst hSortedSecond (fun member => ?_)
  cases hMemFirst : dlDnfHasClause member first with
  | true =>
    rw [dlCanonicalMemberTransfers first second hAntiFirst hClausesFirst hClausesSecond hAgree
        member hMemFirst]
  | false =>
    cases hMemSecond : dlDnfHasClause member second with
    | true =>
      have hBack : dlDnfHasClause member first = true :=
        dlCanonicalMemberTransfers second first hAntiSecond hClausesSecond hClausesFirst
          (fun env => (hAgree env).symm) member hMemSecond
      rw [hMemFirst] at hBack
      exact Bool.noConfusion hBack
    | false => rfl

/-! ## ROUND 2 — STEP 8: SOUNDNESS, the biconditional, and the decision -/

/-- ★★ **SOUNDNESS** — convertible trees have EQUAL canonical minimal-DNF antichains.  The previously walled
`⟹` half, now closed by semantic uniqueness: convertibility gives evaluation agreement
(`distributiveLatticeTreeConv_eval_sound`), every tree evaluates through its canonical DNF (`dlEvalViaDnf`),
both canonical DNFs carry the three canonicity invariants (`dlSortedDnfOf` / `dlClausesSortedDnfOf` /
`dlDnfOfAntichain`), and canonical DNFs computing the same monotone Boolean function are unique
(`dlCanonicalDnfUnique`). -/
theorem distributiveLatticeTreeConv_sound {source target : LatticeTree}
    (conv : DistributiveLatticeTreeConv source target) : dnfOf source = dnfOf target :=
  dlCanonicalDnfUnique (dnfOf source) (dnfOf target)
    (dlSortedDnfOf source) (dlSortedDnfOf target)
    (dlClausesSortedDnfOf source) (dlClausesSortedDnfOf target)
    (dlDnfOfAntichain source) (dlDnfOfAntichain target)
    (fun env => (dlEvalViaDnf env source).symm.trans
      ((distributiveLatticeTreeConv_eval_sound conv env).trans (dlEvalViaDnf env target)))

/-- ★★ **THE NORMAL-FORM BICONDITIONAL** — two trees are convertible in the free bounded distributive
lattice on `ℕ` EXACTLY when their canonical minimal-DNF antichains are structurally equal.  Soundness is
`distributiveLatticeTreeConv_sound`; completeness is `distributiveLatticeTreeConv_complete`. -/
theorem distributiveLatticeTreeConv_iff_normalForm (source target : LatticeTree) :
    DistributiveLatticeTreeConv source target ↔ dnfOf source = dnfOf target :=
  Iff.intro (fun conv => distributiveLatticeTreeConv_sound conv)
    (fun dnfEq => distributiveLatticeTreeConv_complete dnfEq)

/-- **Structural DNF equality** — `List (List Nat)` Boolean equality via `dlClauseBeq`. -/
def dlDnfBeq : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | headFirst :: tailFirst, headSecond :: tailSecond =>
      match dlClauseBeq headFirst headSecond with
      | true => dlDnfBeq tailFirst tailSecond
      | false => false

/-- `dlDnfBeq` cons equation (EQUAL heads): defer to the tails. -/
theorem dlDnfBeqConsTrue (headFirst headSecond : List Nat) (tailFirst tailSecond : List (List Nat))
    (h : dlClauseBeq headFirst headSecond = true) :
    dlDnfBeq (headFirst :: tailFirst) (headSecond :: tailSecond) = dlDnfBeq tailFirst tailSecond := by
  show (match dlClauseBeq headFirst headSecond with
        | true => dlDnfBeq tailFirst tailSecond
        | false => false) = dlDnfBeq tailFirst tailSecond
  rw [h]

/-- `dlDnfBeq` cons equation (DISTINCT heads): refuted. -/
theorem dlDnfBeqConsFalse (headFirst headSecond : List Nat) (tailFirst tailSecond : List (List Nat))
    (h : dlClauseBeq headFirst headSecond = false) :
    dlDnfBeq (headFirst :: tailFirst) (headSecond :: tailSecond) = false := by
  show (match dlClauseBeq headFirst headSecond with
        | true => dlDnfBeq tailFirst tailSecond
        | false => false) = false
  rw [h]

/-- `dlDnfBeq` is reflexive. -/
theorem dlDnfBeqRefl : (dnf : List (List Nat)) → dlDnfBeq dnf dnf = true
  | [] => rfl
  | clause :: rest => by
      rw [dlDnfBeqConsTrue clause clause rest rest (dlClauseBeqRefl clause)]
      exact dlDnfBeqRefl rest

/-- `dlDnfBeq` decides equality: `true` forces the DNFs equal. -/
theorem dlDnfBeqEq : (first second : List (List Nat)) → dlDnfBeq first second = true → first = second := by
  intro first
  induction first with
  | nil =>
    intro second h
    cases second with
    | nil => rfl
    | cons headSecond tailSecond => exact Bool.noConfusion h
  | cons headFirst tailFirst ih =>
    intro second h
    cases second with
    | nil => exact Bool.noConfusion h
    | cons headSecond tailSecond =>
      cases hHead : dlClauseBeq headFirst headSecond with
      | false =>
        rw [dlDnfBeqConsFalse headFirst headSecond tailFirst tailSecond hHead] at h
        exact Bool.noConfusion h
      | true =>
        rw [dlDnfBeqConsTrue headFirst headSecond tailFirst tailSecond hHead] at h
        rw [dlClauseBeqEq headFirst headSecond hHead, ih tailSecond h]

/-- ★ **The Boolean decider** — compare the canonical minimal-DNF antichains structurally. -/
def dlDecideConv (source target : LatticeTree) : Bool :=
  dlDnfBeq (dnfOf source) (dnfOf target)

/-- ★★ **THE DECISION** — `DistributiveLatticeTreeConv source target` holds iff the canonical-DNF decider
returns `true`.  Forward: soundness rewrites the decider to a `dlDnfBeq` reflexivity.  Backward: `dlDnfBeqEq`
feeds completeness. -/
theorem distributiveLatticeTreeConv_iff_decide (source target : LatticeTree) :
    DistributiveLatticeTreeConv source target ↔ dlDecideConv source target = true := by
  constructor
  · intro conv
    show dlDnfBeq (dnfOf source) (dnfOf target) = true
    rw [distributiveLatticeTreeConv_sound conv]
    exact dlDnfBeqRefl (dnfOf target)
  · intro hDecide
    exact distributiveLatticeTreeConv_complete (dlDnfBeqEq (dnfOf source) (dnfOf target) hDecide)

/-- ★ **Decidability of `DistributiveLatticeTreeConv`** — from the canonical-DNF decision, with no `propext`
(the bridge is `Iff.mp` / `Iff.mpr`, never a Prop rewrite). -/
instance dlDecidableConv (source target : LatticeTree) :
    Decidable (DistributiveLatticeTreeConv source target) :=
  if hDecide : dlDecideConv source target = true then
    isTrue ((distributiveLatticeTreeConv_iff_decide source target).mpr hDecide)
  else
    isFalse (fun conv => hDecide ((distributiveLatticeTreeConv_iff_decide source target).mp conv))

/-- Kernel pin (POSITIVE): join-absorbs-meet `join(g0, meet(g0, g1)) ≈ g0` decided `true` by `rfl`. -/
theorem dlDecideConv_absorbsPin :
    dlDecideConv
      (LatticeTree.joinOp (LatticeTree.gen 0)
        (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1)))
      (LatticeTree.gen 0) = true := rfl

/-- Kernel pin (NEGATIVE): `meet(g0, g1)` vs `join(g0, g1)` decided `false` by `rfl` — the headline
two-operation separation. -/
theorem dlDecideConv_separatesMeetJoinPin :
    dlDecideConv
      (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1))
      (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1)) = false := rfl

/-! ## The decision marker -/

/-- ★★ **The walking bounded distributive lattice on an ARBITRARY alphabet — CONVERTIBILITY IS A GENUINE,
COMPLETE DECISION.**  `= true` records that the soundness this file previously walled at
(`fxWalkingDistributiveLattice_minimizationWall := false`, now SUPERSEDED and deleted) is closed:
`DistributiveLatticeTreeConv source target ↔ dnfOf source = dnfOf target`
(`distributiveLatticeTreeConv_iff_normalForm`), with the Boolean decider `dlDecideConv`, the decision
biconditional `distributiveLatticeTreeConv_iff_decide`, and the `Decidable` instance `dlDecidableConv`.

The soundness (`⟹`) half did NOT go through Conv-invariance of the minimizer (the route walled after two
honest rounds — the 12-law congruence does not obviously commute with `removeSupersets`).  It is the
SEMANTIC UNIQUENESS of the minimal-DNF antichain (Quine's uniqueness of the irredundant DNF of a positive
Boolean function; Balbes–Dwinger's free bounded distributive lattice as ⊆-minimal antichains):

* **evaluation through the canonical form** — `dlEvalClause` / `dlEvalDnf` with the comb bridges
  `dlEvalMeetOfClause` / `dlEvalCombOfDnf` and `dlEvalViaDnf` (`evalLatticeTree env tree = dlEvalDnf env
  (dnfOf tree)`), riding the round-1 reduction `dlTreeReducesToDnfComb`;
* **characteristic environments** — `dlCharacteristicEnv` with the unconditional bridges `dlEvalClauseChar`
  (`= clauseSubset`) and `dlEvalDnfChar` (`= dnfHasSubsetOf`): the Boolean function of a DNF, probed at
  `chi(clause)` points, computes the absorption scan;
* **the three canonicity invariants of `dnfOf`** — DNF-level strict sortedness (`dlIsSortedDnf` +
  `dlSortedDnfOf`, threaded through `removeSupersets` / `insertClauseSorted` / `insertClause` / `dnfUnion` /
  `dnfMeetClause` / `dnfMeet` on the back of `dlClauseLessTrans`), clause-level sorted-distinctness
  (`dlAreClausesSorted` + `dlClausesSortedDnfOf` via `dlSortedClauseInsert` / `dlSortedClauseInsertMany`),
  and the ⊆-ANTICHAIN property (`dlDnfIsAntichain` + `dlDnfOfAntichain` via the membership decompositions
  `dlMemRemoveSupersets` / `dlMemInsertClauseSorted` / `dlMemInsertClause` and `dlInsertClauseAntichain`);
* **prime-implicant recovery and uniqueness** — `dlCanonicalMemberTransfers` (a member clause of one
  canonical DNF is recovered inside any evaluation-equal canonical DNF through the `chi(member)` and
  `chi(member \ {missing})` probes, the antichain forcing minimality), sorted-DNF extensionality
  `dlSortedDnfMembersEq` (equal membership on strictly sorted lists is list equality, via the new order kit
  `dlClauseLessIrrefl` / `dlClauseLessAsymm` / `dlClauseLessTrans`), and `dlCanonicalDnfUnique`;
* **the decision** — `distributiveLatticeTreeConv_sound`, the biconditional
  `distributiveLatticeTreeConv_iff_normalForm`, the decider `dlDecideConv` (structural `dlDnfBeq`), the
  decision biconditional, the `Decidable` instance, and the positive / negative kernel pins.

All declarations are zero-axiom: the ordering is the imported structural `natBle` (no `Nat.le` / `Nat.ble`
library lemma), every scan is cons-only, environments are only ever applied (no `funext`), the existentials
are plain inductive `Exists` eliminations, and no `List.append` (`++`), `Int`, `omega`, `decide`-on-`Prop`,
or wildcard match arm appears anywhere. -/
def fxWalkingDistributiveLattice_hasNormalFormDecision : Bool := true

/-! ## Genuineness smokes — the decider fires on TRUE and FALSE instances -/

-- absorption: `join(g0, meet(g0, g1)) ≈ g0` — expected `true`
#eval dlDecideConv
  (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1)))
  (LatticeTree.gen 0)
-- distributivity: `meet(g0, join(g1, g2)) ≈ join(meet(g0, g1), meet(g0, g2))` — expected `true`
#eval dlDecideConv
  (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.joinOp (LatticeTree.gen 1) (LatticeTree.gen 2)))
  (LatticeTree.joinOp (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1))
    (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 2)))
-- distinct generators — expected `false` (REJECTION)
#eval dlDecideConv (LatticeTree.gen 0) (LatticeTree.gen 1)
-- MEET vs JOIN of the same generators — expected `false` (REJECTION, the two-operation headline)
#eval dlDecideConv
  (LatticeTree.meetOp (LatticeTree.gen 0) (LatticeTree.gen 1))
  (LatticeTree.joinOp (LatticeTree.gen 0) (LatticeTree.gen 1))
-- top identity: `meet(g0, ⊤) ≈ g0` — expected `true`
#eval dlDecideConv (LatticeTree.meetOp (LatticeTree.gen 0) LatticeTree.topOp) (LatticeTree.gen 0)
-- bottom identity: `join(g0, ⊥) ≈ g0` — expected `true`
#eval dlDecideConv (LatticeTree.joinOp (LatticeTree.gen 0) LatticeTree.botOp) (LatticeTree.gen 0)
-- top vs bottom — expected `false` (REJECTION)
#eval dlDecideConv LatticeTree.topOp LatticeTree.botOp

end FX1Poly.Polygraph

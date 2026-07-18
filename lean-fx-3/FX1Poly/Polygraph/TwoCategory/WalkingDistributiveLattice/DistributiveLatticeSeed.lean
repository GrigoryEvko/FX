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

## What this file ships (REDUCTION + COMPLETENESS + the absorption lever) — and the honest residual wall

The biconditional `Conv s t ↔ dnfOf s = dnfOf t` now has its `⟸` (COMPLETENESS) half fully closed: every tree
reduces to the join-of-meets comb of its own minimal-DNF antichain (`dlTreeReducesToDnfComb`), so equal
canonical DNFs are convertible (`distributiveLatticeTreeConv_complete`).  This is exactly what the DL's own
absorption law `absorbJoinMeet` unblocks — a ⊆-superset clause is absorbed in a join by its subset
(`dlSupersetAbsorbedInJoin`), which makes the antichain minimization (`removeSupersets` / `insertClause`)
convertibility-invariant.  The residual wall has shrunk to the single `⟹` (SOUNDNESS) lemma
`DistributiveLatticeTreeConv s t → dnfOf s = dnfOf t` — the free-distributive-lattice faithfulness (the
minimal-antichain form is a faithful canonical representative of the monotone Boolean function).  That is the
named blocking node (see `fxWalkingDistributiveLattice_minimizationWall`); it is NOT faked, sorried, or
asserted, and once it lands the `Decidable` decision follows immediately.

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
  the completeness groundings `distributiveLatticeCommViaCompleteness` and `distributiveLatticeReductionRoundtrips`.

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
holds is the walled node below; here it is confirmed on the grounding by kernel computation.) -/
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
form.  This is the `⟸` half of the intended `Conv s t ↔ dnfOf s = dnfOf t` decision; the `⟹` half (soundness)
is the residual wall.  Zero-axiom (only a plain `LatticeTree` equality transported into `Conv`). -/
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

/-! ## The wall marker -/

/-- ★ **The walking bounded distributive lattice on an ARBITRARY alphabet — the absorption lever, the full
minimal-DNF REDUCTION, and COMPLETENESS are now LANDED; the residual wall has shrunk to exactly the SOUNDNESS
(`⟹`) half of the biconditional.**  `= false` records the honest state — one direction of
`Conv s t ↔ dnfOf s = dnfOf t` is still open, so no total decider ships yet:

* LANDED (zero-axiom): the `LatticeTree` carrier, the `Bool`-lattice evaluation `evalLatticeTree`, the
  `DistributiveLatticeTreeConv` fourteen-law convertibility, `distributiveLatticeTreeConv_eval_sound` (a genuine
  sound separator deciding NON-convertibility), the distributivity / meet-absorb-join / join-absorb-meet
  positive groundings, the distinct-generator and MEET-≠-JOIN negative groundings, and the complete minimal-DNF
  antichain machinery `genMember` / `clauseSubset` / the clause order / `insertClause` / `dnfUnion` / `dnfMeet` /
  `dnfJoin` / `canonicalizeDnf` / `dnfOf` / `combOfDnf`.

* LANDED THIS ROUND (zero-axiom, the absorption lever `absorbJoinMeet` finally exploited): the crux
  `dlSupersetAbsorbedInJoin` (a ⊆-superset clause is absorbed in a join by its subset — via `dlClauseUnionMeet`
  + `dlGenMemberMeet` re-meet idempotency), making the antichain minimization convertibility-invariant; the meet
  fragment normalization `dlMeetInsertSortedSet` / `dlMeetMergeClause`; the comb reduction lemmas
  `dlCombInsertClauseSorted` / `dlHasSubsetAbsorbed` / `dlCombJoinRemoveSupersets` / `dlCombInsertClause` /
  `dlCombDnfUnion` / `dlCombDnfMeetClause` / `dlCombDnfMeet` / `dlCombDnfJoin` (each DNF operation computes the
  tree up to `Conv`); the **normalization** `dlTreeReducesToDnfComb` (`tree ≈ combOfDnf (dnfOf tree)`); and the
  **completeness** `distributiveLatticeTreeConv_complete` (`dnfOf s = dnfOf t → Conv s t`) — the `⟸` half of the
  decision — with the completeness groundings `distributiveLatticeCommViaCompleteness` /
  `distributiveLatticeReductionRoundtrips` proving nontrivial convertibilities from `rfl` on `dnfOf` alone.

* STILL WALLED — the exact residual is the SINGLE remaining lemma **`distributiveLatticeTreeConv_sound :
  DistributiveLatticeTreeConv s t → dnfOf s = dnfOf t`** (the `⟹` / soundness half).  It is the
  free-distributive-lattice FAITHFULNESS: that the minimal-DNF antichain is a faithful canonical representative
  of the monotone Boolean function (equivalently, that `dnfMeet` / `dnfJoin` satisfy the fourteen laws as
  STRUCTURAL `List (List Nat)` equalities on minimized antichains, OR that `∀ env, eval s = eval t` forces
  `dnfOf s = dnfOf t`).  This is the uniqueness of the prime-implicant / minimal-antichain representative — the
  analogue of the free-group / abelian-group confluence — and is left UNDECLARED (not sorried, not asserted).
  Once it lands, `decideDistributiveLatticeTreeConv` + `_iff_dnf` + the `Decidable` instance follow immediately
  and this marker flips to `fxWalkingDistributiveLattice_hasDnfDecision := true`.

All landed declarations are zero-axiom: the ordering is the imported structural `natBle` (no `Nat.le`/`Nat.ble`
lemma), the clause inserts are cons-only, and no `List.append` (`++`) or `Int` appears anywhere. -/
def fxWalkingDistributiveLattice_minimizationWall : Bool := false

end FX1Poly.Polygraph

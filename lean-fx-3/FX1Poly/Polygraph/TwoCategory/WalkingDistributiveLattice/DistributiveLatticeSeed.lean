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

## What this file ships (a SOUNDNESS-based partial decision) — and the honest wall

The full DNF-structural biconditional decision `Conv s t ↔ dnfOf s = dnfOf t` is blocked on the
antichain-minimization confluence: the `⟹` (soundness) direction needs `dnfMeet` / `dnfJoin` to satisfy the
distributive-lattice identities as STRUCTURAL `List (List Nat)` equalities on canonical DNFs — equivalently that
the minimal-antichain form is a faithful canonical representative of the monotone Boolean function.  That
free-distributive-lattice confluence / faithfulness is the named blocking node (see
`fxWalkingDistributiveLattice_minimizationWall`); it is NOT faked, sorried, or asserted.

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
  smokes confirming it SEPARATES meet from join and REFLECTS absorption (`dnfOf (∧ g0 (∨ g0 g1)) = [[0]]`).

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

/-! ## The wall marker -/

/-- ★ **The walking bounded distributive lattice on an ARBITRARY alphabet — the minimal-DNF antichain
scaffolding is BUILT and a SOUND semantic decision core is SHIPPED, but the full DNF-structural biconditional is
WALLED at antichain-minimization confluence.**  `= false` records the honest state:

* LANDED (zero-axiom): the `LatticeTree` carrier, the `Bool`-lattice evaluation `evalLatticeTree`, the
  `DistributiveLatticeTreeConv` fourteen-law convertibility, `distributiveLatticeTreeConv_eval_sound` (a genuine
  sound separator deciding NON-convertibility), the distributivity / meet-absorb-join / join-absorb-meet
  positive groundings, the distinct-generator and MEET-≠-JOIN negative groundings, and the complete minimal-DNF
  antichain machinery `genMember` / `clauseSubset` / the clause order / `insertClause` / `dnfUnion` / `dnfMeet` /
  `dnfJoin` / `canonicalizeDnf` / `dnfOf` / `combOfDnf` (computing the canonical form, with smokes confirming it
  SEPARATES meet from join and REFLECTS absorption).

* WALLED — the exact blocking node: **antichain-minimization confluence** = the well-definedness of `dnfMeet` /
  `dnfJoin` as a distributive lattice on canonical DNFs.  The full biconditional `Conv s t ↔ dnfOf s = dnfOf t`
  needs its `⟹` (soundness) direction, which requires the distributive-lattice identities (meet/join
  commutativity, associativity, idempotency, mutual absorption, and distributivity) to hold as STRUCTURAL
  `List (List Nat)` equalities on the minimized antichain forms — equivalently that the minimal-DNF antichain is
  a FAITHFUL canonical representative of the monotone Boolean function.  That free-distributive-lattice
  confluence / faithfulness is the analogue of the free-group / abelian-group confluence and is not closed here;
  it is left UNDECLARED (not sorried, not asserted).

All landed declarations are zero-axiom: the ordering is the imported structural `natBle` (no `Nat.le`/`Nat.ble`
lemma), the clause inserts are cons-only, and no `List.append` (`++`) or `Int` appears anywhere. -/
def fxWalkingDistributiveLattice_minimizationWall : Bool := false

end FX1Poly.Polygraph

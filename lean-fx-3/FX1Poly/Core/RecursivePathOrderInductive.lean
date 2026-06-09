import FX1Poly.Core.MultisetOrder

/-! # FX1Poly/Core/RecursivePathOrderInductive
    — #1139 (Leg 3): the genuine INDUCTIVE recursive path order on a rose-tree term algebra, defined
    zero-axiom (positivity-accepted) and shown to ORIENT the firing-68 branch-duplication obstruction arm
    that defeats every flat measure

Firing-67 (`IotaNonRecursiveTermination`) gave the 13 NON-recursive ι arms a clean `RawTerm.size`-decrease
SN.  Firing-68 (`RecursiveIotaSizeGrowth`) proved the RECURSIVE arm `natElim (succ n) z s ↝ app (app s n)
(elim n z s)` INCREASES `RawTerm.size` by `branch.size + 5`, growing without bound — so NO flat numeric
measure certifies it.  The branch `s` is DUPLICATED (it appears in both `app s n` and the recursive
`elim n z s`), and a flat multiset of scrutinee-sizes fails for the same reason: the duplicated copies of
`s`'s internal eliminators are ADDED with no corresponding removal, which is not a Dershowitz-Manna step.

The honest resolution — the standard one for primitive recursion / Gödel's T ι-rules — is a genuine
RECURSIVE PATH ORDER (RPO) whose multiset comparison is over the RPO relation ITSELF (recursively), with a
precedence `eliminator > app` on the head symbols.  The single-level certificates in `RecursivePathOrder`
(`wellFounded_of_precedence{Lex,Multiset}Measure`) compare head precedence then the IMMEDIATE-argument
multiset over a FIXED base order — they do not recurse into subterms, so they cannot certify the
congruence-closed recursive ι.  This file builds the genuine inductive RPO that does.

## What this ships

  * `RoseTerm Symbol` — the generic rose-tree term algebra (`mkGen gen children` of `RawTerm` instantiates
    it: gen ↦ symbol, children ↦ child list).  The RPO is generic so it ports to `RawTerm` directly.
  * `Rpo prec` — the inductive recursive path order with MULTISET status (`Rpo prec big small` reads
    `big ≻ small`).  Four clauses: `subtermEq` (a node dominates each direct child), `subtermStrict` (a node
    dominates anything a child dominates — the subterm property), `precedence` (higher head precedence, and
    the bigger dominates every reduct child), and `multiset` (equal head, the argument multiset
    Dershowitz-Manna-decreases under `Rpo` itself, and the bigger dominates every reduct child).
  * **`rpo_orients_natElim` (★)** — the RPO ORIENTS the firing-68 obstruction arm: `redex ≻ reduct` for
    `natElim (succ n) z s ≻ app (app s n) (elim n z s)`, for an ARBITRARY branch `s` (faithful
    branch-duplication).  This is exactly the arm no flat measure could orient (firing-68); the subterm
    property tames the duplication regardless of `s`'s size.
  * **`fxPrecedence_wellFounded` (★)** — the head precedence is well-founded (the first ingredient of RPO
    well-foundedness): `eliminator > app > succ > zero` is the inverse image of `Nat.lt` under a rank.

## Positivity (the genuine Lean hurdle this firing cleared)

Two kernel obstructions, both solved:
  * The subterm clause is SPLIT into `subtermEq` / `subtermStrict` rather than written with a single
    `subtermChild = small ∨ Rpo prec subtermChild small` premise — the kernel treats `Or` applied to the
    inductive-being-defined as a NESTED inductive whose parameters may not contain the local variables, and
    rejects it.  Splitting removes the `Or`.
  * The `multiset` clause INLINES the Dershowitz-Manna witnesses (`removed`, `prefix`/`suffix`/`added`
    lists, and the two `∀ … → Rpo prec …` premises) directly, rather than carrying `MultisetRedOne (Rpo
    prec)` as a premise — passing the inductive-being-defined as a relation argument to the external
    `MultisetRedOne` def is rejected by the strict-positivity checker (it cannot see the positive use).
    Inlined, every `Rpo` occurrence sits strictly positively to the right of `∀`/`→`.

## Well-foundedness (the Nipkow/Buchholz nested accessibility — PROVED here)

**`rpoWellFounded` (★)**: `WellFounded prec → WellFounded (RpoBelow prec)` where `RpoBelow prec small big :=
Rpo prec big small`.  The proof needs no `size` measure: it uses the rose-tree recursor TWICE.  `acc_node`
(a node with all children RPO-accessible is accessible) is proved by outer induction on the head's
precedence-accessibility and inner induction on the children's MULTISET accessibility (supplied by the
shipped `MultisetRedOne.consAccessible` from each child's accessibility); the `Acc.intro` body `predAcc` is
then built by the rose-tree recursor on the PREDECESSOR, so the precedence/multiset cases get the
predecessor's children accessible — breaking the apparent circularity structurally.  `fxRpoWellFounded`
instantiates it at `fxPrecedence`, so the eliminator-fragment RPO (which `rpo_orients_natElim` shows orients
the firing-68 obstruction arm) is a genuine well-founded order — the complete termination certificate for
that arm.  The β boundary stays honestly Tait-imported (raw β is non-SN — Ω, SN-NECESSITY #950); #1139
separates the terminating ι/η fragment from it.

The `Rpo` inversion (`cases` on a doubly-`node`-indexed `Rpo` proof) is propext-clean here (verified), so the
four-clause case analysis in `acc_node_mult` introduces no axioms.

## Zero-axiom verification

The inductive is strictly positive (subterm-split + inlined multiset witnesses); the orientation is by the
four constructors + `List.Mem.head`/`.tail` (propext-free) + `decide` on closed `Nat` `<`; precedence-WF is
`InvImage.wf` of `Nat.lt`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core.RpoInductive

/-- Generic rose-tree term algebra: a head symbol applied to a list of child terms.
    `RawTerm`'s `mkGen gen children` instantiates this (gen ↦ symbol, children ↦ child list). -/
inductive RoseTerm (Symbol : Type) where
  | node : Symbol → List (RoseTerm Symbol) → RoseTerm Symbol

variable {Symbol : Type}

/-- The recursive path order with multiset status.  `Rpo prec big small` reads `big ≻ small`.
    `prec smallSym bigSym` reads `bigSym ≻F smallSym` (precedence on heads).
    The subterm clause is SPLIT into `subtermEq`/`subtermStrict` (no `∨`, which the kernel would treat as a
    nested inductive forbidding the local `Rpo` occurrence); the multiset clause's witnesses are INLINED
    (not via the external `MultisetRedOne (Rpo prec)`, which strict-positivity rejects). -/
inductive Rpo (prec : Symbol → Symbol → Prop) : RoseTerm Symbol → RoseTerm Symbol → Prop where
  | subtermEq (headSym : Symbol) (children : List (RoseTerm Symbol))
      (subtermChild : RoseTerm Symbol) :
      subtermChild ∈ children →
      Rpo prec (.node headSym children) subtermChild
  | subtermStrict (headSym : Symbol) (children : List (RoseTerm Symbol))
      (smaller subtermChild : RoseTerm Symbol) :
      subtermChild ∈ children →
      Rpo prec subtermChild smaller →
      Rpo prec (.node headSym children) smaller
  | precedence (bigSym : Symbol) (bigChildren : List (RoseTerm Symbol))
      (smallSym : Symbol) (smallChildren : List (RoseTerm Symbol)) :
      prec smallSym bigSym →
      (∀ smallChild, smallChild ∈ smallChildren →
        Rpo prec (.node bigSym bigChildren) smallChild) →
      Rpo prec (.node bigSym bigChildren) (.node smallSym smallChildren)
  | multiset (headSym : Symbol) (bigChildren smallChildren : List (RoseTerm Symbol))
      (removed : RoseTerm Symbol)
      (prefixChildren suffixChildren addedChildren : List (RoseTerm Symbol)) :
      bigChildren = prefixChildren ++ removed :: suffixChildren →
      smallChildren = prefixChildren ++ addedChildren ++ suffixChildren →
      (∀ addedChild, addedChild ∈ addedChildren → Rpo prec removed addedChild) →
      (∀ smallChild, smallChild ∈ smallChildren →
        Rpo prec (.node headSym bigChildren) smallChild) →
      Rpo prec (.node headSym bigChildren) (.node headSym smallChildren)

/-- A concrete eliminator-fragment symbol set: app, zero, succ, elim. -/
inductive FxElimSym where
  | appSym | zeroSym | succSym | elimSym

/-- Precedence rank: `elim` outranks `app` outranks the constructors. -/
def precedenceRank : FxElimSym → Nat
  | .zeroSym => 0
  | .succSym => 1
  | .appSym => 2
  | .elimSym => 3

/-- The precedence: a smaller rank is `≻F`-below a bigger one. -/
def fxPrecedence (smallSym bigSym : FxElimSym) : Prop :=
  precedenceRank smallSym < precedenceRank bigSym

abbrev FxTerm := RoseTerm FxElimSym

/-- `natElim (succ n) z s` redex (firing-68's obstruction arm), faithful branch `s`. -/
def natElimRedex (predScrut zeroBranch succBranch : FxTerm) : FxTerm :=
  .node .elimSym [.node .succSym [predScrut], zeroBranch, succBranch]

/-- Its reduct `app (app s n) (elim n z s)` — branch `s` DUPLICATED. -/
def natElimReduct (predScrut zeroBranch succBranch : FxTerm) : FxTerm :=
  .node .appSym
    [.node .appSym [succBranch, predScrut],
     .node .elimSym [predScrut, zeroBranch, succBranch]]

/-- `node f children ≻ n` whenever a direct `succ`-child holds `n`: the `succ n ≻ n` step packaged. -/
private theorem rpo_via_succ_child (predScrut : FxTerm) (headSym : FxElimSym)
    (children : List FxTerm) (membership : (.node .succSym [predScrut]) ∈ children) :
    Rpo fxPrecedence (.node headSym children) predScrut :=
  Rpo.subtermStrict headSym children predScrut (.node .succSym [predScrut]) membership
    (Rpo.subtermEq .succSym [predScrut] predScrut (List.Mem.head _))

/-- **The RPO orients the firing-68 obstruction arm** — `redex ≻ reduct` despite branch-duplication.
The reduct's outer head is `app`, below the redex's `elim` in the precedence, and the redex dominates each
reduct child: `app s n` (again by precedence, dominating `s` and `n` as subterms) and the recursive
`elim n z s` (same head, multiset step `[succ n] ↦ [n]` since `succ n ≻ n`).  No flat measure could orient
this (firing-68); the subterm property tames the duplicated `s` regardless of its size. -/
theorem rpo_orients_natElim (predScrut zeroBranch succBranch : FxTerm) :
    Rpo fxPrecedence (natElimRedex predScrut zeroBranch succBranch)
      (natElimReduct predScrut zeroBranch succBranch) := by
  dsimp only [natElimRedex, natElimReduct]
  -- redex ≻ app(app s n)(elim n z s) by precedence (elim ≻F app), redex ≻ each child
  refine Rpo.precedence (bigSym := FxElimSym.elimSym) (bigChildren := _)
    (smallSym := FxElimSym.appSym) (smallChildren := _) ?_ ?_
  · exact (by decide : precedenceRank .appSym < precedenceRank .elimSym)
  · intro smallChild membership
    rcases membership with _ | ⟨_, membershipRest⟩
    · -- child = app s n : redex ≻ app s n by precedence (elim ≻F app), redex ≻ s, redex ≻ n
      refine Rpo.precedence (bigSym := FxElimSym.elimSym) (bigChildren := _)
        (smallSym := FxElimSym.appSym) (smallChildren := _) ?_ ?_
      · exact (by decide : precedenceRank .appSym < precedenceRank .elimSym)
      · intro innerChild innerMembership
        rcases innerMembership with _ | ⟨_, innerRest⟩
        · -- s : direct subterm (3rd child of redex)
          exact Rpo.subtermEq .elimSym _ succBranch
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        · rcases innerRest with _ | ⟨_, innerEmpty⟩
          · -- n : subterm via succ child
            exact rpo_via_succ_child predScrut .elimSym _ (List.Mem.head _)
          · nomatch innerEmpty
    · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
      · -- child = elim n z s : same head, multiset step [succ n] ↦ [n] (succ n ≻ n)
        refine Rpo.multiset _ _ _ (.node .succSym [predScrut]) [] [zeroBranch, succBranch]
          [predScrut] rfl rfl ?_ ?_
        · intro addedChild addedMembership
          rcases addedMembership with _ | ⟨_, addedEmpty⟩
          · exact Rpo.subtermEq .succSym _ predScrut (List.Mem.head _)
          · nomatch addedEmpty
        · intro smallChild smallMembership
          rcases smallMembership with _ | ⟨_, smallRest⟩
          · -- n : subterm via succ child
            exact rpo_via_succ_child predScrut .elimSym _ (List.Mem.head _)
          · rcases smallRest with _ | ⟨_, smallRest2⟩
            · -- z : direct subterm (2nd child)
              exact Rpo.subtermEq .elimSym _ zeroBranch (List.Mem.tail _ (List.Mem.head _))
            · rcases smallRest2 with _ | ⟨_, smallEmpty⟩
              · -- s : direct subterm (3rd child)
                exact Rpo.subtermEq .elimSym _ succBranch
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              · nomatch smallEmpty
      · nomatch membershipEmpty

/-- **The precedence is well-founded** (the first ingredient of RPO well-foundedness): a smaller
`precedenceRank` is below a bigger, so `fxPrecedence` is the inverse image of `Nat.lt` under the rank. -/
theorem fxPrecedence_wellFounded : WellFounded fxPrecedence :=
  InvImage.wf precedenceRank Nat.lt_wfRel.wf

variable {prec : Symbol → Symbol → Prop}

/-- `RpoBelow prec small big` = `small` is RPO-below `big` (the order whose well-foundedness we prove).
Reducible so `cases` sees through it to the `Rpo` constructors during inversion. -/
@[reducible] def RpoBelow (prec : Symbol → Symbol → Prop) (small big : RoseTerm Symbol) : Prop :=
  Rpo prec big small

/-- Children all accessible ⟹ the children-list is multiset-accessible (fold of `consAccessible`). -/
theorem childrenMultisetAcc {children : List (RoseTerm Symbol)}
    (accChildren : ∀ child, child ∈ children → Acc (RpoBelow prec) child) :
    Acc (MultisetRedOne (RpoBelow prec)) children := by
  induction children with
  | nil => exact MultisetRedOne.emptyAccessible _
  | cons headChild tailChildren ih =>
      exact MultisetRedOne.consAccessible _ headChild
        (accChildren headChild (List.Mem.head _)) tailChildren
        (ih (fun child membership => accChildren child (List.Mem.tail _ membership)))

/-- The genuine `acc_node`, parameterized on the precedence IH and the children's MULTISET accessibility
(inducted on as the inner argument).  `predAcc` (the `Acc.intro` body) is built by the rose-tree recursor on
the predecessor, so the precedence/multiset cases get the predecessor's children accessible — breaking the
apparent circularity without any `size` measure. -/
theorem acc_node_mult (headSym : Symbol)
    (ihPrec : ∀ otherSym, prec otherSym headSym → ∀ otherChildren,
      (∀ child, child ∈ otherChildren → Acc (RpoBelow prec) child) →
      Acc (RpoBelow prec) (.node otherSym otherChildren))
    (children : List (RoseTerm Symbol))
    (accMult : Acc (MultisetRedOne (RpoBelow prec)) children) :
    (∀ child, child ∈ children → Acc (RpoBelow prec) child) →
    Acc (RpoBelow prec) (.node headSym children) := by
  induction accMult with
  | intro children _accMultPred ihMult =>
    intro accChildren
    apply Acc.intro
    refine RoseTerm.rec
      (motive_1 := fun term => RpoBelow prec term (.node headSym children) → Acc (RpoBelow prec) term)
      (motive_2 := fun childList => ∀ child, child ∈ childList →
        (RpoBelow prec child (.node headSym children) → Acc (RpoBelow prec) child))
      ?nodeCase ?nilCase ?consCase
    case nodeCase =>
      intro smallSym smallChildren predChildren hBelow
      cases hBelow with
      | subtermEq _ _ _ membership => exact accChildren _ membership
      | subtermStrict _ _ _ subtermChild membership inner =>
          exact Acc.inv (accChildren subtermChild membership) inner
      | precedence _ _ _ _ precProof reductChildrenBelow =>
          exact ihPrec smallSym precProof smallChildren
            (fun child membership => predChildren child membership (reductChildrenBelow child membership))
      | multiset _ _ _ removed prefixChildren suffixChildren addedChildren
          bigEq smallEq addedSmaller reductChildrenBelow =>
          exact ihMult smallChildren
            ⟨removed, prefixChildren, suffixChildren, addedChildren, bigEq, smallEq, addedSmaller⟩
            (fun child membership => predChildren child membership (reductChildrenBelow child membership))
    case nilCase => intro child membership; nomatch membership
    case consCase =>
      intro headChild tailChildren headInductive tailInductive child membership
      rcases membership with _ | ⟨_, memberTail⟩
      · exact headInductive
      · exact tailInductive child memberTail

/-- **`acc_node`**: a node with all children RPO-accessible is itself RPO-accessible — outer induction on the
head's precedence-accessibility, supplying `acc_node_mult` with the children's multiset accessibility. -/
theorem acc_node (headSym : Symbol) (accPrec : Acc prec headSym) :
    ∀ children, (∀ child, child ∈ children → Acc (RpoBelow prec) child) →
    Acc (RpoBelow prec) (.node headSym children) := by
  induction accPrec with
  | intro headSym _accPrecPred ihPrec =>
    intro children accChildren
    exact acc_node_mult headSym ihPrec children (childrenMultisetAcc accChildren) accChildren

/-- The structural wrapper: RPO well-foundedness follows from `acc_node`, by the rose-tree recursor. -/
theorem rpoBelow_wellFoundedOfAccNode
    (accNode : ∀ (headSym : Symbol) (children : List (RoseTerm Symbol)),
      (∀ child, child ∈ children → Acc (RpoBelow prec) child) →
      Acc (RpoBelow prec) (.node headSym children)) :
    WellFounded (RpoBelow prec) :=
  WellFounded.intro fun term =>
    RoseTerm.rec
      (motive_1 := fun t => Acc (RpoBelow prec) t)
      (motive_2 := fun cs => ∀ child, child ∈ cs → Acc (RpoBelow prec) child)
      (fun headSym children childrenAcc => accNode headSym children childrenAcc)
      (fun child membership => nomatch membership)
      (fun _headChild tailChildren headAcc tailAcc child membership => by
        rcases membership with _ | ⟨_, memberTail⟩
        · exact headAcc
        · exact tailAcc child memberTail)
      term

/-- **★ RPO well-foundedness**: the recursive path order over a well-founded precedence is well-founded.
The genuinely-hard Nipkow/Buchholz nested-accessibility theorem, zero-axiom, no `size` measure. -/
theorem rpoWellFounded (precWellFounded : WellFounded prec) :
    WellFounded (RpoBelow prec) :=
  rpoBelow_wellFoundedOfAccNode fun headSym children accChildren =>
    acc_node headSym (precWellFounded.apply headSym) children accChildren

/-- **★ The eliminator-fragment RPO is well-founded**: instantiating `rpoWellFounded` at `fxPrecedence`.
Together with `rpo_orients_natElim`, the firing-68 obstruction arm sits in a genuine well-founded order —
the complete termination certificate for it. -/
theorem fxRpoWellFounded : WellFounded (RpoBelow fxPrecedence) :=
  rpoWellFounded fxPrecedence_wellFounded

/-! ### RPO congruence (compatibility with contexts)

The well-founded order above orients root redexes.  To use it as a *rewrite* termination certificate we also
need it to be a **congruence**: replacing one child of a node by an RPO-smaller child makes the whole node
RPO-smaller.  This is the monotonicity that lifts a child-context ι step (`StepChildren`) to a node-level RPO
decrease.  Proved via the `multiset` clause — the single child replacement is a Dershowitz-Manna multiset
decrease — with the unchanged children dominated as subterms and the replacement dominated through the larger
child.  The four `List` helpers below are propext-clean re-proofs of the `Init` append/membership facts the
clause needs (`List.append_assoc` and friends leak `propext`). -/

/-- Propext-clean `(prefix ++ [x]) ++ suffix = prefix ++ x :: suffix` (the `List.append_assoc` route leaks
propext; this is a `congrArg` induction on the prefix). -/
private theorem appendSingletonMiddle {Elem : Type} (prefixList : List Elem) (singleElem : Elem)
    (suffixList : List Elem) :
    (prefixList ++ [singleElem]) ++ suffixList = prefixList ++ singleElem :: suffixList := by
  induction prefixList with
  | nil => rfl
  | cons headElem _tailList ih => exact congrArg (headElem :: ·) ih

/-- `x ∈ l1 → x ∈ l1 ++ l2` (propext-clean, `List.Mem` induction on the left list). -/
private theorem memAppendOfMemLeft {Elem : Type} {element : Elem} {rightList : List Elem} :
    ∀ {leftList : List Elem}, element ∈ leftList → element ∈ leftList ++ rightList := by
  intro leftList
  induction leftList with
  | nil => intro membership; nomatch membership
  | cons _headElem _tailList ih =>
      intro membership
      rcases membership with _ | ⟨_, membershipTail⟩
      · exact List.Mem.head _
      · exact List.Mem.tail _ (ih membershipTail)

/-- `x ∈ l2 → x ∈ l1 ++ l2` (propext-clean). -/
private theorem memAppendOfMemRight {Elem : Type} {element : Elem} {rightList : List Elem}
    (membership : element ∈ rightList) : ∀ {leftList : List Elem}, element ∈ leftList ++ rightList := by
  intro leftList
  induction leftList with
  | nil => exact membership
  | cons _headElem _tailList ih => exact List.Mem.tail _ ih

/-- `x ∈ l1 ++ l2 → x ∈ l1 ∨ x ∈ l2` (propext-clean). -/
private theorem memAppendCases {Elem : Type} {element : Elem} {rightList : List Elem} :
    ∀ {leftList : List Elem}, element ∈ leftList ++ rightList → element ∈ leftList ∨ element ∈ rightList := by
  intro leftList
  induction leftList with
  | nil => intro membership; exact Or.inr membership
  | cons _headElem _tailList ih =>
      intro membership
      rcases membership with _ | ⟨_, membershipTail⟩
      · exact Or.inl (List.Mem.head _)
      · rcases ih membershipTail with inLeft | inRight
        · exact Or.inl (List.Mem.tail _ inLeft)
        · exact Or.inr inRight

/-- **★ The RPO is a congruence**: replacing one child `bigChild` of a node by an RPO-smaller `smallChild`
makes the whole node RPO-smaller.  Via the multiset clause (the argument multiset Dershowitz-Manna-decreases
by the single replacement), with the unchanged children dominated as subterms and `smallChild` dominated
through `bigChild`.  This is the monotonicity / compatibility-with-contexts of RPO — the property that turns
it from a root-redex order into a genuine rewrite order. -/
theorem rpo_congruence (headSym : Symbol)
    (prefixChildren suffixChildren : List (RoseTerm Symbol))
    (bigChild smallChild : RoseTerm Symbol) (hstep : Rpo prec bigChild smallChild) :
    Rpo prec (.node headSym (prefixChildren ++ bigChild :: suffixChildren))
      (.node headSym (prefixChildren ++ smallChild :: suffixChildren)) := by
  refine Rpo.multiset headSym _ _ bigChild prefixChildren suffixChildren [smallChild] rfl
    (appendSingletonMiddle prefixChildren smallChild suffixChildren).symm ?_ ?_
  · intro addedChild addedMembership
    rcases addedMembership with _ | ⟨_, addedEmpty⟩
    · exact hstep
    · nomatch addedEmpty
  · intro reductChild reductMembership
    rcases memAppendCases reductMembership with inPrefix | inSmallSuffix
    · exact Rpo.subtermEq headSym _ reductChild (memAppendOfMemLeft inPrefix)
    · rcases inSmallSuffix with _ | ⟨_, inSuffix⟩
      · exact Rpo.subtermStrict headSym _ smallChild bigChild
          (memAppendOfMemRight (List.Mem.head _)) hstep
      · exact Rpo.subtermEq headSym _ reductChild (memAppendOfMemRight (List.Mem.tail _ inSuffix))

/-- The head-child special case (`prefix = []`): if the FIRST child steps RPO-down, the node steps RPO-down.
The form the kernel's `StepChildren` head-step maps to. -/
theorem rpo_congruence_head (headSym : Symbol) (restChildren : List (RoseTerm Symbol))
    (bigChild smallChild : RoseTerm Symbol) (hstep : Rpo prec bigChild smallChild) :
    Rpo prec (.node headSym (bigChild :: restChildren)) (.node headSym (smallChild :: restChildren)) :=
  rpo_congruence headSym [] restChildren bigChild smallChild hstep

end FX1Poly.Core.RpoInductive
